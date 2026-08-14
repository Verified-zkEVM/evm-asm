/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashKeccak

  Shared keccak setup/call + compare rounds + success ambient + adapter
  helpers for `header_validate_parent_hash` match/mismatch arms.
  Same namespace as `HeaderValidateParentHashSpec`.
-/

import EvmAsm.Codegen.Programs.HeaderValidateParentHashSpec

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

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
      | exact bytesRegion_pcFree _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _)

/-! ## Success-path setup (instr 13–16 at `H+52`): parent → a0/a1; `la a2, computed` -/

set_option maxRecDepth 8000 in
/-- After extract-ok: `mv a0,s0` ;; `mv a1,s1` ;; `la a2, hvph_computed`.
    Leaves PC at `H+68` — the `jal zkvm_keccak256` site. -/
theorem hvphKeccakSetup
    (spC ret link parentPtr parentLen old10 old11 old12 : Word) (vals : Reg → Word) :
    cpsTripleWithin 4 (H + 52) (H + 68) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ parentPtr) ** (.x11 ↦ᵣ parentLen) ** (.x12 ↦ᵣ Computed) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have h0 := mv_spec_gen_within .x10 .x8 parentPtr old10 (H + 52) (by decide)
  have h1 := mv_spec_gen_within .x11 .x9 parentLen old11 (H + 56) (by decide)
  have e0 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 52) hvphProg 13 (.MV .x10 .x8)
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) h0
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 56) hvphProg 14 (.MV .x11 .x9)
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) h1
  have hau := CodeReq.ofProg_mem_at H (H + 60) hvphProg 15
    (.AUIPC .x12 (EvmAsm.Codegen.laHi GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 60)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had := CodeReq.ofProg_mem_at H (H + 64) hvphProg 16
    (.ADDI .x12 .x12 (EvmAsm.Codegen.laLo GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 60)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla := EvmAsm.Rv64.la_materialize_within .x12 old12 (H + 60) Computed (by decide)
    (by unfold H Computed; decide) hau had
  have e0F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) e0
  have e1F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) **
      (.x18 ↦ᵣ vals .x18) ** (.x10 ↦ᵣ parentPtr) ** (.x12 ↦ᵣ old12) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) e1
  have hlaF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x10 ↦ᵣ parentPtr) ** (.x11 ↦ᵣ parentLen) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e0F e1F
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hlaF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Keccak call at `H+68` (proven leaf, not a premise) -/

theorem stackFree4_eq_keccakFrameSlotsOwn (sp : Word) :
    stackFree sp 4 =
      frameSlotsOwn keccakFrame (sp + signExtend12 (-32 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 4)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 1)) ** empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (24 : BitVec 12)) ** empAssertion)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-32 : Word) + (0 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-32 : Word) + (8 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-32 : Word) + (16 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-32 : Word) + (24 : Word) from by bv_omega]

theorem hvph_keccak_jal_disj :
    (CodeReq.singleton (H + 68)
      (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
        (GuestAddrs.header_validate_parent_hash + 68)))).Disjoint keccakCode :=
  CodeReq.Disjoint.singleton_ofProg (by decide)

theorem hvph_keccak_jal_mem :
    ∀ a i, CodeReq.singleton (H + 68)
        (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.header_validate_parent_hash + 68))) a = some i →
      fullCode a = some i :=
  fun a i h => hvph_mono a i (hvph_keccak_jal_oneshot.1 a i h)

/-- Step count of the one-shot keccak leaf. -/
abbrev nKeccak (N rem : Nat) : Nat := 5 + keccakBodyFuel N rem + 6

set_option maxRecDepth 8000 in
/-- `jal zkvm_keccak256` at `H+68` under the proven leaf (returns `H+72`).

    Requires `stackFree spC 4` for keccak's frame, parent RLP as input, and the
    `hvph_computed` out-buffer.  HVPH frame / claimed / this-bytes live in `F`. -/
theorem hvphKeccakCall
    (spC ret : Word)
    (parentPtr : Word) (parentBytes : List (BitVec 8))
    (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    let lenW := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
    let out0 := List.replicate 32 (0 : BitVec 8)
    let kvals := keccakEntryVals v8 v9 v18 v20
    cpsTripleWithin (1 + nKeccak N rem) (H + 68) (H + 72) fullCode
      ((.x1 ↦ᵣ ret) ** (.x2 ↦ᵣ spC) **
        (stackFree spC 4 ** regsAt keccakFrame kvals **
          keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
            empAssertion) ** F)
      ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          regsAt keccakFrame kvals **
          keccakCallerPost parentPtr Computed parentBytes N rem empAssertion) ** F) := by
  intro lenW out0 kvals
  have htarget : (H + 68) + signExtend21 (jalOff GuestAddrs.zkvm_keccak256
      (GuestAddrs.header_validate_parent_hash + 68)) = K := by
    change BitVec.ofNat 64 GuestAddrs.header_validate_parent_hash + BitVec.ofNat 64 68 + _ =
      BitVec.ofNat 64 GuestAddrs.zkvm_keccak256
    exact jalOff_correct_add GuestAddrs.zkvm_keccak256
      GuestAddrs.header_validate_parent_hash 68
      (by decide) (by decide) (by decide) (by decide)
  have hret72 : ((H + 72 : Word) &&& ~~~(1 : Word)) = H + 72 := by decide
  have hcallee0 := zkvm_keccak256_spec_within spC (H + 72)
    parentPtr Computed parentBytes N rem v8 v9 v18 v20 v28 v29 os empAssertion
    (by pcf) hret72 hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hcallee' :
      cpsTripleWithin (nKeccak N rem) K (H + 72) keccakCode
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 72)) **
          regsAt keccakFrame kvals **
          frameSlotsOwn keccakFrame (spC + signExtend12 (-32 : BitVec 12)) **
          keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
            empAssertion)
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (H + 72)) **
          regsAt keccakFrame kvals **
          frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          keccakCallerPost parentPtr Computed parentBytes N rem empAssertion) := by
    simp only [nKeccak, lenW, out0, kvals, K, keccakCode] at hcallee0 ⊢
    simpa [K, keccakCode] using hcallee0
  rw [← stackFree4_eq_keccakFrameSlotsOwn spC] at hcallee'
  have hcalleeFull :
      cpsTripleWithin (nKeccak N rem) K (H + 72) fullCode
        ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
          (stackFree spC 4 ** regsAt keccakFrame kvals **
            keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
              empAssertion))
        ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
          (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
            regsAt keccakFrame kvals **
            keccakCallerPost parentPtr Computed parentBytes N rem empAssertion)) := by
    have h := cpsTripleWithin_extend_code keccak_mono hcallee'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h
  have hcallPc : (H + 68 : Word) + 4 = H + 72 := by bv_omega
  have hcall := abiFrameCall_spec (cr := fullCode)
    (calleePre := stackFree spC 4 ** regsAt keccakFrame kvals **
      keccakCallerPre parentPtr lenW Computed v28 v29 os parentBytes out0
        empAssertion)
    (calleePost := frameSlotsSaved keccakFrame
        (spC + signExtend12 (-32 : BitVec 12)) kvals **
      regsAt keccakFrame kvals **
      keccakCallerPost parentPtr Computed parentBytes N rem empAssertion)
    (F := F) (H + 68) K ret spC
    (jalOff GuestAddrs.zkvm_keccak256
      (GuestAddrs.header_validate_parent_hash + 68))
    0 (nKeccak N rem)
    htarget
    hvph_keccak_jal_mem
    (by
      refine pcFree_sepConj (pcFree_stackFree _ _)
        (pcFree_sepConj (pcFree_regsAt _ _) ?_)
      exact keccakCallerPre_pcFree parentPtr lenW Computed v28 v29 os parentBytes out0
        empAssertion (by pcf))
    hF
    (by
      simpa only [hcallPc, stackFree_zero, sepConj_emp_left', sepConj_emp_right',
        nKeccak] using hcalleeFull)
  simpa only [stackFree_zero, sepConj_emp_left', hcallPc, nKeccak] using hcall

set_option maxRecDepth 8000 in
/-- Keccak setup (`H+52`) ;; leaf call (`H+68`) → `H+72`. Cost `5+nK`. -/
theorem hvphKeccakSetupAndCall
    (spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (old10 old11 old12 v20 v28 v29 : Word)
    (parentBytes : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hplen : parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor parentPtr N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    let out0 := List.replicate 32 (0 : BitVec 8)
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    cpsTripleWithin (5 + nKeccak N rem) (H + 52) (H + 72) fullCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x10 ↦ᵣ old10) ** (.x11 ↦ᵣ old11) ** (.x12 ↦ᵣ old12) **
        (.x20 ↦ᵣ v20) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 ** F)
      ((.x1 ↦ᵣ (H + 72)) ** (.x2 ↦ᵣ spC) **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          regsAt keccakFrame kvals **
          keccakCallerPost parentPtr Computed parentBytes N rem empAssertion) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) ** F) := by
  intro out0 kvals
  let lenW : Word := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
  have hsetup0 := hvphKeccakSetup spC ret link parentPtr parentLen old10 old11 old12 vals
  have hsetup := cpsTripleWithin_extend_code hvph_mono <|
    cpsTripleWithin_frameR
      ((.x20 ↦ᵣ v20) ** stackFree spC 4 **
        (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
        bytesRegion parentPtr parentBytes **
        bytesRegion Computed out0 ** F)
      (by refine pcFree_sepConj ?_ (pcFree_sepConj (pcFree_stackFree _ _)
            (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
              (pcFree_sepConj (pcFree_regOwns _) (pcFree_sepConj (bytesRegion_pcFree _ _)
                (pcFree_sepConj (bytesRegion_pcFree _ _)
                  (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))))))
          <;> pcf) hsetup0
  have hcall := hvphKeccakCall spC link parentPtr parentBytes N rem
    parentPtr parentLen (vals .x18) v20 v28 v29 os
    (frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) ** F)
    (by refine pcFree_sepConj ?_ hF; pcf)
    hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hregs : regsAt keccakFrame kvals =
      ((.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ lenW) ** (.x18 ↦ᵣ vals .x18) **
        (.x20 ↦ᵣ v20)) := by
    have hlenW : parentLen = lenW := by simp only [lenW]; exact hplen
    simp [kvals, keccakEntryVals, keccakFrame, regsAt, sepConj_emp_right', hlenW]
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    have hlenW : parentLen = lenW := by simp only [lenW]; exact hplen
    rw [hlenW] at hp
    unfold keccakCallerPre
    rw [hregs, sepConj_emp_right']
    xperm_hyp hp) hsetup hcall
  have hn : 4 + (1 + nKeccak N rem) = 5 + nKeccak N rem := by omega
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Compare setup (instr 18–21 at `H+72`): `la t0,claimed` ;; `la t1,computed` -/

set_option maxRecDepth 8000 in
/-- After keccak returns: materialize Claimed/Computed bases into `x5`/`x6`.
    Leaves PC at `H+88` — first `LD` of the 4-dword compare. -/
theorem hvphCompareSetup
    (spC ret link parentPtr parentLen : Word) (vals : Reg → Word)
    (old5 old6 : Word) :
    cpsTripleWithin 4 (H + 72) (H + 88) hvphCode
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ old5) ** (.x6 ↦ᵣ old6) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals))
      ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) **
        (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) ** (.x18 ↦ᵣ vals .x18) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) := by
  have hau5 := CodeReq.ofProg_mem_at H (H + 72) hvphProg 18
    (.AUIPC .x5 (EvmAsm.Codegen.laHi GuestAddrs.hvph_claimed
      (GuestAddrs.header_validate_parent_hash + 72)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had5 := CodeReq.ofProg_mem_at H (H + 76) hvphProg 19
    (.ADDI .x5 .x5 (EvmAsm.Codegen.laLo GuestAddrs.hvph_claimed
      (GuestAddrs.header_validate_parent_hash + 72)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla5 := EvmAsm.Rv64.la_materialize_within .x5 old5 (H + 72) Claimed (by decide)
    (by unfold H Claimed; decide) hau5 had5
  have hau6 := CodeReq.ofProg_mem_at H (H + 80) hvphProg 20
    (.AUIPC .x6 (EvmAsm.Codegen.laHi GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 80)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have had6 := CodeReq.ofProg_mem_at H (H + 84) hvphProg 21
    (.ADDI .x6 .x6 (EvmAsm.Codegen.laLo GuestAddrs.hvph_computed
      (GuestAddrs.header_validate_parent_hash + 80)))
    (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)
  have hla6 := EvmAsm.Rv64.la_materialize_within .x6 old6 (H + 80) Computed (by decide)
    (by unfold H Computed; decide) hau6 had6
  have hla5F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x6 ↦ᵣ old6) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla5
  have hla6F := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ link) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
      (.x18 ↦ᵣ vals .x18) ** (.x5 ↦ᵣ Claimed) **
      frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals)) (by pcf) hla6
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla5F hla6F
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## Status-0 / status-2 exits (match → `li a0,0` ;; `j` ;; epi; mismatch → `li a0,2` ;; epi) -/

set_option maxRecDepth 8000 in
/-- Match exit: `li a0, 0` @ `H+136` → `j` skip status-2 → epilogue. -/
theorem hvphStatus0Exit
    (sp0 spC o10 : Word) (vals vals' : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 8 (H + 136) (vals .x1) hvphCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (0 : Word) (H + 136) (by decide)
  have s1 := jal_x0_spec_gen_within (8 : BitVec 21) (H + 140)
  rw [show (H + 140) + signExtend21 (8 : BitVec 21) = H + 148 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega] at s1
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 136) hvphProg 34 (.LI .x10 (0 : Word))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s0
  have s1C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 140) hvphProg 35 (.JAL .x0 (8 : BitVec 21))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s1
  have hblock : cpsTripleWithin 2 (H + 136) (H + 148) hvphCode
      ((.x10 ↦ᵣ o10)) ((.x10 ↦ᵣ (0 : Word))) := by
    runBlock s0C s1C
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))
        <;> pcf) hblock
  have hepi := hvphEpi sp0 spC (0 : Word) vals vals' G hG hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Mismatch exit: `li a0, 2` @ `H+144` → epilogue. -/
theorem hvphStatus2Exit
    (sp0 spC o10 : Word) (vals vals' : Reg → Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1) :
    cpsTripleWithin 7 (H + 144) (vals .x1) hvphCode
      ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) **
        regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals ** G) := by
  have s0 := li_spec_gen_within .x10 o10 (2 : Word) (H + 144) (by decide)
  have s0C := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 144) hvphProg 36 (.LI .x10 (2 : Word))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) s0
  have hblockF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG))
        <;> pcf) s0C
  have hepi := hvphEpi sp0 spC (2 : Word) vals vals' G hG hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hblockF hepi
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

/-! ## 4-dword compare (instr 22–33): LD claimed ;; LD computed ;; BNE → status-2

    Equal fall-through advances `+12` per round; mismatch BNE targets `H+144`. -/

abbrev dwordAt (bs : List (BitVec 8)) (q : Nat) : Word :=
  packBytes ((bs.drop (8 * q)).take 8)

set_option maxRecDepth 8000 in
/-- Round 0 equal: `LD/LD/BNE` at `H+88` fall through to `H+100`. -/
theorem hvphCompareRound0Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 0 = dwordAt computedBytes 0) :
    cpsTripleWithin 3 (H + 88) (H + 100) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 88) claimedBytes 0
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 88) hvphProg 22 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 92) computedBytes 0
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 92) hvphProg 23 (.LD .x28 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 0) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (48 : BitVec 13)
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) (H + 96)
  rw [show (H + 96 : Word) + 4 = H + 100 from by bv_omega,
    show (H + 96) + signExtend13 (48 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (48 : BitVec 13) = (48 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 96) hvphProg 24 (.BNE .x7 .x28 (48 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 0 mismatch: `LD/LD/BNE` at `H+88` taken to `H+144` (status-2 site). -/
theorem hvphCompareRound0Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    cpsTripleWithin 3 (H + 88) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 88) claimedBytes 0
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 88) hvphProg 22 (.LD .x7 .x5 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 92) computedBytes 0
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 92) hvphProg 23 (.LD .x28 .x6 (0 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 0) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (48 : BitVec 13)
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) (H + 96)
  rw [show (H + 96 : Word) + 4 = H + 100 from by bv_omega,
    show (H + 96) + signExtend13 (48 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (48 : BitVec 13) = (48 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 96) hvphProg 24 (.BNE .x7 .x28 (48 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 1 equal: `H+100` → `H+112`. -/
theorem hvphCompareRound1Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 1 = dwordAt computedBytes 1) :
    cpsTripleWithin 3 (H + 100) (H + 112) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 100) claimedBytes 1
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 100) hvphProg 25 (.LD .x7 .x5 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 104) computedBytes 1
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 104) hvphProg 26 (.LD .x28 .x6 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 1) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (36 : BitVec 13)
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) (H + 108)
  rw [show (H + 108 : Word) + 4 = H + 112 from by bv_omega,
    show (H + 108) + signExtend13 (36 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 108) hvphProg 27 (.BNE .x7 .x28 (36 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 1 mismatch: `H+100` → `H+144`. -/
theorem hvphCompareRound1Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 1 ≠ dwordAt computedBytes 1) :
    cpsTripleWithin 3 (H + 100) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 100) claimedBytes 1
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 100) hvphProg 25 (.LD .x7 .x5 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 104) computedBytes 1
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 104) hvphProg 26 (.LD .x28 .x6 (8 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 1) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (36 : BitVec 13)
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) (H + 108)
  rw [show (H + 108 : Word) + 4 = H + 112 from by bv_omega,
    show (H + 108) + signExtend13 (36 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (36 : BitVec 13) = (36 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 108) hvphProg 27 (.BNE .x7 .x28 (36 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 2 equal: `H+112` → `H+124`. -/
theorem hvphCompareRound2Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 2 = dwordAt computedBytes 2) :
    cpsTripleWithin 3 (H + 112) (H + 124) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 112) claimedBytes 2
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 112) hvphProg 28 (.LD .x7 .x5 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 116) computedBytes 2
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 116) hvphProg 29 (.LD .x28 .x6 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 2) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (24 : BitVec 13)
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) (H + 120)
  rw [show (H + 120 : Word) + 4 = H + 124 from by bv_omega,
    show (H + 120) + signExtend13 (24 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 120) hvphProg 30 (.BNE .x7 .x28 (24 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 2 mismatch: `H+112` → `H+144`. -/
theorem hvphCompareRound2Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 2 ≠ dwordAt computedBytes 2) :
    cpsTripleWithin 3 (H + 112) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 112) claimedBytes 2
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 112) hvphProg 28 (.LD .x7 .x5 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 116) computedBytes 2
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 116) hvphProg 29 (.LD .x28 .x6 (16 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 2) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (24 : BitVec 13)
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) (H + 120)
  rw [show (H + 120 : Word) + 4 = H + 124 from by bv_omega,
    show (H + 120) + signExtend13 (24 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (24 : BitVec 13) = (24 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 120) hvphProg 30 (.BNE .x7 .x28 (24 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 3 equal: `H+124` → `H+136` (status-0 site). -/
theorem hvphCompareRound3Eq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_eq : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    cpsTripleWithin 3 (H + 124) (H + 136) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 124) claimedBytes 3
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 124) hvphProg 31 (.LD .x7 .x5 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 128) computedBytes 3
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 128) hvphProg 32 (.LD .x28 .x6 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 3) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (12 : BitVec 13)
    (dwordAt claimedBytes 3) (dwordAt computedBytes 3) (H + 132)
  rw [show (H + 132 : Word) + 4 = H + 136 from by bv_omega,
    show (H + 132) + signExtend13 (12 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 132) hvphProg 33 (.BNE .x7 .x28 (12 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have hfall0 := cpsBranchWithin_ntakenStripPure2 hbneC
    (fun _ hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 h_eq)
  have hfall := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) hfall0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 hfall
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Round 3 mismatch: `H+124` → `H+144`. -/
theorem hvphCompareRound3Ne
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 3 ≠ dwordAt computedBytes 3) :
    cpsTripleWithin 3 (H + 124) (H + 144) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have hld1 := bytesRegion_ld_within .x7 .x5 Claimed v7 (H + 124) claimedBytes 3
    (by decide) (by omega) (by decide)
  have e1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 124) hvphProg 31 (.LD .x7 .x5 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld1
  have e1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ Computed) ** (.x28 ↦ᵣ v28) ** bytesRegion Computed computedBytes)
    (by pcf) e1
  have hld2 := bytesRegion_ld_within .x28 .x6 Computed v28 (H + 128) computedBytes 3
    (by decide) (by omega) (by decide)
  have e2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 128) hvphProg 32 (.LD .x28 .x6 (24 : BitVec 12))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hld2
  have e2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x7 ↦ᵣ dwordAt claimedBytes 3) ** claimedOwn claimedBytes)
    (by pcf) e2
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) e1F e2F
  have hbne := bne_spec_gen_within .x7 .x28 (12 : BitVec 13)
    (dwordAt claimedBytes 3) (dwordAt computedBytes 3) (H + 132)
  rw [show (H + 132 : Word) + 4 = H + 136 from by bv_omega,
    show (H + 132) + signExtend13 (12 : BitVec 13) = H + 144 from by
      rw [show signExtend13 (12 : BitVec 13) = (12 : Word) from by decide]; bv_omega] at hbne
  have hbneC := cpsBranchWithin_extend_code
    (CodeReq.ofProg_mem_at H (H + 132) hvphProg 33 (.BNE .x7 .x28 (12 : BitVec 13))
      (by bv_omega) (by rw [hvph_length]; decide) rfl (by rw [hvph_length]; decide)) hbne
  have htake0 := cpsBranchWithin_takenStripPure2 hbneC
    (fun _ hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact h_ne ((sepConj_pure_right _).1 hBP).2)
  have htake := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes) (by pcf) htake0
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 htake
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- All four dwords equal: `H+88` → `H+136` (12 steps). -/
theorem hvphCompareAllEq
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 : Word)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    cpsTripleWithin 12 (H + 88) (H + 136) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes)
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Eq claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h1
  have r2 := hvphCompareRound2Eq claimedBytes computedBytes
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) hclen hcdlen h2
  have r3 := hvphCompareRound3Eq claimedBytes computedBytes
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) hclen hcdlen h3
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 r3
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Match residual from compare start: all-eq ;; status-0 exit. Cost `20`. -/
theorem hvphCompareMatchExit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h3 : dwordAt claimedBytes 3 = dwordAt computedBytes 3) :
    cpsTripleWithin 20 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have hcmp0 := hvphCompareAllEq claimedBytes computedBytes v7 v28 hclen hcdlen h0 h1 h2 h3
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus0Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : 12 + 8 = 20 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- First-dword mismatch residual: round0-ne ;; status-2 exit. Cost `10`. -/
theorem hvphCompareMismatch0Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h_ne : dwordAt claimedBytes 0 ≠ dwordAt computedBytes 0) :
    cpsTripleWithin 10 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have hcmp0 := hvphCompareRound0Ne claimedBytes computedBytes v7 v28 hclen hcdlen h_ne
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 0) ** (.x28 ↦ᵣ dwordAt computedBytes 0) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : 3 + 7 = 10 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Dword-1 mismatch: eq0 ;; ne1 ;; status-2. Cost `13`. -/
theorem hvphCompareMismatch1Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h_ne : dwordAt claimedBytes 1 ≠ dwordAt computedBytes 1) :
    cpsTripleWithin 13 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Ne claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h_ne
  have hcmp0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 1) ** (.x28 ↦ᵣ dwordAt computedBytes 1) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : (3 + 3) + 7 = 13 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Dword-2 mismatch: eq0–1 ;; ne2 ;; status-2. Cost `16`. -/
theorem hvphCompareMismatch2Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h_ne : dwordAt claimedBytes 2 ≠ dwordAt computedBytes 2) :
    cpsTripleWithin 16 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Eq claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h1
  have r2 := hvphCompareRound2Ne claimedBytes computedBytes
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) hclen hcdlen h_ne
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have hcmp0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 2) ** (.x28 ↦ᵣ dwordAt computedBytes 2) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : (3 + 3 + 3) + 7 = 16 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall

set_option maxRecDepth 8000 in
/-- Dword-3 mismatch: eq0–2 ;; ne3 ;; status-2. Cost `19`. -/
theorem hvphCompareMismatch3Exit
    (sp0 spC _ret : Word) (vals vals' : Reg → Word)
    (claimedBytes computedBytes : List (BitVec 8))
    (v7 v28 o10 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hret : vals .x1 &&& ~~~(1 : Word) = vals .x1)
    (hclen : claimedBytes.length = 32) (hcdlen : computedBytes.length = 32)
    (h0 : dwordAt claimedBytes 0 = dwordAt computedBytes 0)
    (h1 : dwordAt claimedBytes 1 = dwordAt computedBytes 1)
    (h2 : dwordAt claimedBytes 2 = dwordAt computedBytes 2)
    (h_ne : dwordAt claimedBytes 3 ≠ dwordAt computedBytes 3) :
    cpsTripleWithin 19 (H + 88) (vals .x1) hvphCode
      ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x10 ↦ᵣ o10) **
        (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' ** frameSlotsSaved hvphFrame spC vals **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ vals .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) ** (.x18 ↦ᵣ vals .x18) **
        frameSlotsSaved hvphFrame spC vals **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
        claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G) := by
  have r0 := hvphCompareRound0Eq claimedBytes computedBytes v7 v28 hclen hcdlen h0
  have r1 := hvphCompareRound1Eq claimedBytes computedBytes
    (dwordAt claimedBytes 0) (dwordAt computedBytes 0) hclen hcdlen h1
  have r2 := hvphCompareRound2Eq claimedBytes computedBytes
    (dwordAt claimedBytes 1) (dwordAt computedBytes 1) hclen hcdlen h2
  have r3 := hvphCompareRound3Ne claimedBytes computedBytes
    (dwordAt claimedBytes 2) (dwordAt computedBytes 2) hclen hcdlen h_ne
  have h01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) r0 r1
  have h012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h01 r2
  have hcmp0 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h012 r3
  have hcmp := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ o10) ** (.x2 ↦ᵣ spC) ** regsAt hvphFrame vals' **
      frameSlotsSaved hvphFrame spC vals ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ hG))) <;> pcf) hcmp0
  have hexi := hvphStatus2Exit sp0 spC o10 vals vals'
    ((.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
      (.x7 ↦ᵣ dwordAt claimedBytes 3) ** (.x28 ↦ᵣ dwordAt computedBytes 3) **
      claimedOwn claimedBytes ** bytesRegion Computed computedBytes ** G)
    (by refine pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_
          (pcFree_sepConj ?_ (pcFree_sepConj ?_ (pcFree_sepConj ?_ hG)))))
        <;> first | exact bytesRegion_pcFree _ _ | pcf) hspC hret
  have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hcmp hexi
  have hn : (3 + 3 + 3 + 3) + 7 = 19 := by decide
  rw [← hn]
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hall


/-! ## From headers return (`H+40`): extract-ok beq ;; keccak ;; compare-match -/

/-- Ambient past the headers frame for the keccak success path.
    Does not include a1/a2 — those are havoc `regOwn` from `headersCallPremise`. -/
def hvphSuccKeccakAmb
    (spC v20 : Word)
    (os out0 : List (BitVec 8))
    (F : Assertion) : Assertion :=
  (.x20 ↦ᵣ v20) **
  stackFree spC 4 **
  regOwns [.x14, .x15, .x16, .x17] **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
  bytesRegion Computed out0 ** F

theorem hvphSuccKeccakAmb_pcFree
    (spC v20 : Word)
    (os out0 : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree) :
    (hvphSuccKeccakAmb spC v20 os out0 F).pcFree := by
  unfold hvphSuccKeccakAmb
  refine pcFree_sepConj ?_ (pcFree_sepConj (pcFree_stackFree _ _)
    (pcFree_sepConj (pcFree_regOwns _)
      (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (bytesRegion_pcFree _ _) hF))))
  · pcf

/-- `headersCallFrameCore` without `x28`/`x29` owns (concrete on keccak success). -/
def headersCallFrameSuccCore
    (spC ret parentPtr parentLen : Word) (vals : Reg → Word)
    (parentBytes : List (BitVec 8)) : Assertion :=
  (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
  (.x18 ↦ᵣ vals .x18) **
  frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
  bytesRegion parentPtr parentBytes **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x13 ** regOwn .x30 ** regOwn .x31


/-! ## Adapter helpers (BSS frame around hvphPre/Post) -/

/-- Reassemble parent bytes from the keccak caller's split free assertion. -/
theorem bytesRegion_of_keccakCallerFreeA
    (parentPtr : Word) (parentBytes : List (BitVec 8)) (N rem : Nat)
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem) :
    ∀ h, (keccakCallerFreeA parentPtr parentBytes N empAssertion) h →
      bytesRegion parentPtr parentBytes h := by
  intro h hp
  unfold keccakCallerFreeA keccakResidual keccakAbsorbCursor at hp
  set n := keccakAbsorbStep * N
  have hpre : (parentBytes.take n).length = n := by
    simp only [n, List.length_take, hlen]; omega
  have hmod : n % 8 = 0 := by
    simp only [n, keccakAbsorbStep]; omega
  have h8 : 8 ∣ (parentBytes.take n).length := by
    rw [hpre]; exact Nat.dvd_of_mod_eq_zero hmod
  have hp2 :
      (bytesRegion parentPtr (parentBytes.take n) **
        bytesRegion (parentPtr + BitVec.ofNat 64 n) (parentBytes.drop n)) h := by
    have hp' :
        (bytesRegion (parentPtr + BitVec.ofNat 64 n) (parentBytes.drop n) **
          bytesRegion parentPtr (parentBytes.take n)) h := by
      simpa [sepConj_emp_right'] using hp
    xperm_hyp hp'
  have happ := bytesRegion_append parentPtr
    (parentBytes.take n) (parentBytes.drop n) h8
  have hfull : bytesRegion parentPtr (parentBytes.take n ++ parentBytes.drop n) h := by
    rw [happ, hpre]
    exact hp2
  simpa [List.take_append_drop] using hfull

/-- Leftover ambient after a match exit (BSS + keccak frame + caller-saved scratch). -/
def hvphMatchExitExtra
    (spC parentPtr parentLen v20 : Word) (vals : Reg → Word)
    (parentBytes claimedBytes digest : List (BitVec 8)) (N rem : Nat)
    (F : Assertion) : Assertion :=
  claimedOwn claimedBytes ** bytesRegion Computed digest **
  frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
    (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
  (.x20 ↦ᵣ v20) **
  bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
    (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
      (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
  regOwns [.x14, .x15, .x16, .x17] **
  F

/-- Keccak-exit residual post → `hvphPost ** Extra` (demote scratch; reassemble parent).
    Parameterized by exit `status` and the concrete compare scratch dwords in x7/x28. -/
theorem hvphKeccakExit_post_to_adapter
    (sp0 spC ret parentPtr parentLen v20 status d7 d28 : Word) (vals : Reg → Word)
    (thisPtr : Word) (thisBytes parentBytes claimedBytes : List (BitVec 8))
    (N rem : Nat) (F : Assertion)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hlen : parentBytes.length = keccakAbsorbStep * N + rem) :
    let digest := keccakBodyDigest parentBytes N rem
    let saved := hvphFrameVals ret vals
    let kvals := keccakEntryVals parentPtr parentLen (vals .x18) v20
    ∀ s,
      ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) s →
      (hvphPost sp0 thisPtr parentPtr ret status vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals
          parentBytes claimedBytes digest N rem F) s := by
  intro digest saved kvals s hq
  -- Reassemble parent, then demote x5/x6/x7/x28.
  have hqTrail :
      ((((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
          frameSlotsSaved hvphFrame spC saved **
          (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
          (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
          claimedOwn claimedBytes ** bytesRegion Computed digest **
          frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          bytesRegion thisPtr thisBytes ** F) **
        keccakCallerFreeA parentPtr parentBytes N empAssertion)) s := by
    xperm_hyp hq
  have hqParent :
      ((((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
          (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
          frameSlotsSaved hvphFrame spC saved **
          (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
          (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
          claimedOwn claimedBytes ** bytesRegion Computed digest **
          frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          bytesRegion thisPtr thisBytes ** F) **
        bytesRegion parentPtr parentBytes)) s :=
    sepConj_mono_right (bytesRegion_of_keccakCallerFreeA parentPtr parentBytes N rem hlen)
      s hqTrail
  -- Rotate each concrete scratch to the front and demote.
  have hx5 : ((.x5 ↦ᵣ Claimed) **
      ((.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp hqParent
  have o5 := sepConj_mono_left (regIs_to_regOwn .x5 Claimed) s hx5
  have hx6 : ((.x6 ↦ᵣ Computed) **
      (regOwn .x5 **
        (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x7 ↦ᵣ d7) ** (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp o5
  have o6 := sepConj_mono_left (regIs_to_regOwn .x6 Computed) s hx6
  have hx7 : ((.x7 ↦ᵣ d7) **
      (regOwn .x6 ** regOwn .x5 **
        (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        (.x28 ↦ᵣ d28) **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp o6
  have o7 := sepConj_mono_left (regIs_to_regOwn .x7 d7) s hx7
  have hx28 : ((.x28 ↦ᵣ d28) **
      (regOwn .x7 ** regOwn .x6 ** regOwn .x5 **
        (.x10 ↦ᵣ status) ** (.x1 ↦ᵣ saved .x1) ** (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ saved .x8) ** (.x9 ↦ᵣ saved .x9) ** (.x18 ↦ᵣ saved .x18) **
        frameSlotsSaved hvphFrame spC saved **
        claimedOwn claimedBytes ** bytesRegion Computed digest **
        frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12)) kvals **
        (.x20 ↦ᵣ v20) **
        bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
          (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
        (.x0 ↦ᵣ (0 : Word)) **
        regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
        bytesRegion thisPtr thisBytes ** F **
        bytesRegion parentPtr parentBytes)) s := by
    xperm_hyp o7
  have o28 := sepConj_mono_left (regIs_to_regOwn .x28 d28) s hx28
  have hx1 : saved .x1 = ret := by simp [saved, hvphFrameVals]
  have hx8 : saved .x8 = vals .x8 := by simp [saved, hvphFrameVals]
  have hx9 : saved .x9 = vals .x9 := by simp [saved, hvphFrameVals]
  have hx18 : saved .x18 = vals .x18 := by simp [saved, hvphFrameVals]
  unfold hvphPost hvphMatchExitExtra
  -- Expand `regsAt` on the goal so it matches the concrete s0/s1/s2 atoms.
  simp only [regsAt_hvphSavedFrame, hx1, hx8, hx9, hx18, kvals, digest, saved, hspC,
    regOwns, sepConj_emp_right'] at o28 ⊢
  xperm_hyp o28

end EvmAsm.Codegen.HeaderValidateParentHashSpec
