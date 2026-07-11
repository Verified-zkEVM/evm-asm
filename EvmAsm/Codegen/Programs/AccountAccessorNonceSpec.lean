/-
  EvmAsm.Codegen.Programs.AccountAccessorNonceSpec

  Lives under Codegen/Programs (not Evm64), mirroring
  `AccountAccessorTopSpec.lean` — see that file's header for the layering
  rationale.

  Split out of `AccountAccessorTopSpec.lean` (file-size guardrail): the
  top-level success-path `cpsTripleWithin` triple for `account_extract_nonce`
  (`accountExtractNonce_prog`, 23 instructions, entry
  `GuestAddrs.account_extract_nonce`): from `a0 = ptr(encodeAccount a)`,
  `a1 = |encodeAccount a|`, `a2 = out ptr`, the body terminates at the
  caller's return address with `a0 = 0` and the u64 output cell holding
  `a.nonce` (`a.nonce < 2^64`, EIP-2681).

  The shared infrastructure — fixed guest addresses, code-layout
  disjointness, the `ownifyN` scratch-ownership helpers, and the
  ownership-precondition callee triples — stays in
  `AccountAccessorTopSpec.lean` (which also carries
  `account_extract_balance`'s top-level triple), which this file imports.
  See that file's header for the full design notes.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountAccessorTopSpec

namespace EvmAsm.Codegen

open EvmAsm.EL
open EvmAsm.EL.RLP
open EvmAsm.Evm64
open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Rv64.Tactics

/-! ## `account_extract_nonce`: success tail (idx 9..16, 19..22) -/

set_option maxRecDepth 8000 in
/-- **Success tail of `account_extract_nonce`** (from `+36`, right after the
    field-0 `rlp_walk_next` success branch): derive the content window, call
    `rlp_content_to_u64` (which decodes the nonce big-endian), store it to the
    output cell, set `a0 = 0`, skip the failure arm, restore `ra`/`s0`/`sp`,
    and return. ∀-quantified over `x5`'s incoming value `t0Old` (trailing
    factor, for `ownify1`). -/
theorem account_extract_nonce_tail_spec_within
    (listBase outPtr raVal s0Old spF x1Val outMid t0Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.nonce).length + 23)
      (extractNonceBase + 36) (raVal &&& ~~~1) accountExtractNonceFullCode
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        (.x1 ↦ᵣ x1Val) ** (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion listBase (encodeAccount a) ** (outPtr ↦ₘ outMid) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old)) **
        (.x5 ↦ᵣ t0Old))
      ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ (spF + 16)) ** (.x8 ↦ᵣ s0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase (encodeAccount a) **
        memOwn spF ** memOwn (spF + 8)) := by
  have hn256 : a.nonce < 2 ^ 256 := by
    have hle : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  set encN := (encodeBytes (Nat.toBytesBE a.nonce)).length with hencN
  set cN := (Nat.toBytesBE a.nonce).length with hcN
  have hcn_le : cN ≤ 2 + encN := by
    obtain ⟨pre, _, hplen⟩ := encodeBytes_toBytesBE_split a.nonce (by
      have := account_nonce_field_len_le_8 a hnonce
      omega)
    omega
  set advanced := listBase + BitVec.ofNat 64 (2 + encN) with hadv
  set cLenW : Word := BitVec.ofNat 64 cN with hcLenW
  set contentPtr := listBase + BitVec.ofNat 64 ((2 + encN) - cN) with hcp
  have hsub_eq : advanced - cLenW = contentPtr := by
    rw [hadv, hcLenW, hcp]
    bv_omega
  -- Glue block idx 9..11 (`+36 → +48`): SUB x5 x10 x12 ; MV x10 x5 ; MV x11 x12.
  have hsub := sub_spec_gen_within .x5 .x10 .x12 advanced cLenW t0Old
    (extractNonceBase + 36) (by decide)
  rw [hsub_eq] at hsub
  have hmv10 := mv_spec_gen_within .x10 .x5 contentPtr advanced (extractNonceBase + 40)
    (by decide)
  have hmv11 := mv_spec_gen_within .x11 .x12 cLenW (0 : Word) (extractNonceBase + 44)
    (by decide)
  have hGlue : cpsTripleWithin 3 (extractNonceBase + 36) (extractNonceBase + 48)
      accountExtractNonceCode
      ((.x10 ↦ᵣ advanced) ** (.x12 ↦ᵣ cLenW) ** (.x5 ↦ᵣ t0Old) ** (.x11 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ contentPtr) ** (.x12 ↦ᵣ cLenW) ** (.x5 ↦ᵣ contentPtr) **
        (.x11 ↦ᵣ cLenW)) := by
    runBlock hsub hmv10 hmv11
  have hGlue' := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ x1Val) ** (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase (encodeAccount a) ** (outPtr ↦ₘ outMid) **
      (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old))
    (by pcFree) (cpsTripleWithin_extend_code aen_sub hGlue)
  -- Call `rlp_content_to_u64` (idx 12, `+48 → +52`).
  have hoffset : (extractNonceBase + 48) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u64
        (Codegen.GuestAddrs.account_extract_nonce + 48)) = contentU64Base := by decide
  have halign : (extractNonceBase + 48 + 4) &&& ~~~(1 : Word) =
      extractNonceBase + 48 + 4 := by decide
  have hdisj : (CodeReq.singleton (extractNonceBase + 48)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u64
        (Codegen.GuestAddrs.account_extract_nonce + 48)))).Disjoint
      (rlp_content_to_u64_code contentU64Base) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len contentU64Base rlp_content_to_u64_prog 22 _
        rlp_content_to_u64_prog_length
        (fun k hk => by unfold extractNonceBase contentU64Base; bv_omega))
  have hcallee_raw := account_rlp_content_to_u64_nonce_own_spec_within
    contentU64Base listBase (extractNonceBase + 48 + 4) contentPtr a hnonce
    hsalign hover hvalid
  rw [← hencN, ← hcN, ← hcp, ← hcLenW] at hcallee_raw
  have hcallee_framed := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cLenW) **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (outPtr ↦ₘ outMid) **
      (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old))
    (by pcFree) hcallee_raw
  have hPrest : (((.x10 ↦ᵣ contentPtr) ** (.x11 ↦ᵣ cLenW) ** (.x5 ↦ᵣ contentPtr) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encodeAccount a) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x28) **
      ((.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cLenW) **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (outPtr ↦ₘ outMid) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old))).pcFree := by
    pcFree
  have hcall := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u64
      (Codegen.GuestAddrs.account_extract_nonce + 48))
    (vOld := x1Val) hoffset halign hPrest hdisj
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hcallee_framed)
  have hmono12 : ∀ a' i,
      ((CodeReq.singleton (extractNonceBase + 48)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_content_to_u64
          (Codegen.GuestAddrs.account_extract_nonce + 48)))).union
        (rlp_content_to_u64_code contentU64Base)) a' = some i →
      accountExtractNonceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aen_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 12
          (extractNonceBase + 48) (by decide) (by decide) (by decide)) a' i h))
      aen_cu64_sub
  have hCall := cpsTripleWithin_extend_code hmono12 hcall
  rw [show (extractNonceBase + 48 + 4 : Word) = extractNonceBase + 52 from by decide]
    at hCall
  -- BNE x11 x0 (idx 13, `+52 → +56`): not taken since the decode status is 0.
  have hbne := bne_spec_gen_within .x11 .x0 (16 : BitVec 13) (0 : Word) (0 : Word)
    (extractNonceBase + 52)
  rw [show (extractNonceBase + 52) + signExtend13 (16 : BitVec 13)
        = extractNonceBase + 68 from by decide,
      show (extractNonceBase + 52 : Word) + 4 = extractNonceBase + 56 from by decide]
    at hbne
  have hmono13 : ∀ a' i, CodeReq.singleton (extractNonceBase + 52)
      (.BNE .x11 .x0 (16 : BitVec 13)) a' = some i →
      accountExtractNonceFullCode a' = some i :=
    fun a' i h => aen_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 13
        (extractNonceBase + 52) (by decide) (by decide) (by decide)) a' i h)
  have hBne := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono13 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (BitVec.ofNat 64 a.nonce)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        (.x1 ↦ᵣ (extractNonceBase + 52)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x12 ↦ᵣ cLenW) **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (outPtr ↦ₘ outMid) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old))
      (by pcFree) hbne))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- SD x8 x10 (idx 14, `+56 → +60`): store the decoded nonce.
  have hsd := sd_spec_gen_within .x8 .x10 outPtr (BitVec.ofNat 64 a.nonce) outMid
    (0 : BitVec 12) (extractNonceBase + 56)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show outPtr + (0 : Word) = outPtr from by bv_omega] at hsd
  -- LI x10 0 (idx 15, `+60 → +64`).
  have hli := li_spec_gen_within .x10 (BitVec.ofNat 64 a.nonce) (0 : Word)
    (extractNonceBase + 60) (by decide)
  have hStore : cpsTripleWithin 2 (extractNonceBase + 56) (extractNonceBase + 64)
      accountExtractNonceCode
      ((.x8 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (BitVec.ofNat 64 a.nonce)) ** (outPtr ↦ₘ outMid))
      ((.x8 ↦ᵣ outPtr) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce))) := by
    runBlock hsd hli
  have hStore' := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ cLenW) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
      regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (extractNonceBase + 52)) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase (encodeAccount a) **
      (.x2 ↦ᵣ spF) ** (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old))
    (by pcFree) (cpsTripleWithin_extend_code aen_sub hStore)
  -- JAL x0 12 (idx 16, `+64 → +76`): skip the failure arm.
  have hjal := jal_x0_spec_gen_within (12 : BitVec 21) (extractNonceBase + 64)
  rw [show (extractNonceBase + 64) + signExtend21 (12 : BitVec 21)
        = extractNonceBase + 76 from by decide] at hjal
  have hmono16 : ∀ a' i, CodeReq.singleton (extractNonceBase + 64)
      (.JAL .x0 (12 : BitVec 21)) a' = some i → accountExtractNonceFullCode a' = some i :=
    fun a' i h => aen_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 16
        (extractNonceBase + 64) (by decide) (by decide) (by decide)) a' i h)
  have hJal : cpsTripleWithin 1 (extractNonceBase + 64) (extractNonceBase + 76)
      accountExtractNonceFullCode
      ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ cLenW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        (.x1 ↦ᵣ (extractNonceBase + 52)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
        (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ cLenW) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        (.x1 ↦ᵣ (extractNonceBase + 52)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
          (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ cLenW) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          (.x1 ↦ᵣ (extractNonceBase + 52)) ** bytesRegion listBase (encodeAccount a) **
          (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
          (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old) ** (.x0 ↦ᵣ (0 : Word)))
        (by pcFree) (cpsTripleWithin_extend_code hmono16 hjal))
  -- Restore block idx 19..22 (`+76 → ra`): LD ra ; LD s0 ; ADDI sp ; JALR.
  have hld1 := ld_spec_gen_within .x1 .x2 spF (extractNonceBase + 52) raVal
    (0 : BitVec 12) (extractNonceBase + 76) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show spF + (0 : Word) = spF from by bv_omega] at hld1
  have hld8 := ld_spec_gen_within .x8 .x2 spF outPtr s0Old
    (8 : BitVec 12) (extractNonceBase + 80) (by decide)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide] at hld8
  have haddi := addi_spec_gen_same_within .x2 spF (16 : BitVec 12)
    (extractNonceBase + 84) (by decide)
  rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide] at haddi
  have hret := jalr_x0_spec_gen_within .x1 raVal (0 : BitVec 12) (extractNonceBase + 88)
  simp only [signExtend12_0] at hret
  rw [show (raVal + 0 : Word) = raVal from by bv_omega] at hret
  have hRestore : cpsTripleWithin 4 (extractNonceBase + 76) (raVal &&& ~~~1)
      accountExtractNonceCode
      ((.x2 ↦ᵣ spF) ** (.x1 ↦ᵣ (extractNonceBase + 52)) ** (.x8 ↦ᵣ outPtr) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old))
      ((.x2 ↦ᵣ (spF + 16)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old)) := by
    runBlock hld1 hld8 haddi hret
  have hRestore' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
      (.x0 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
      regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** bytesRegion listBase (encodeAccount a) **
      regOwn .x11 ** regOwn .x12)
    (by pcFree) (cpsTripleWithin_extend_code aen_sub hRestore)
  -- Compose glue ⨾ call ⨾ BNE ⨾ store ⨾ JAL ⨾ restore.
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hGlue' hCall; intro h hp; xperm_hyp hp
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hBne; intro h hp; xperm_hyp hp
  have s3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s2 hStore'
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have s4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s3 hJal; intro h hp; xperm_hyp hp
  have s5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s4 hRestore'
    intro h hp
    have hp2 := sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (regIs_implies_regOwn .x11)
        (sepConj_mono (regIs_implies_regOwn .x12) (fun _ x => x)))) h hp
    xperm_hyp hp2
  refine cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => ?_) s5)
  -- Release the stack-frame save cells back as raw ownership.
  have hp2 := sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono memIs_implies_memOwn memIs_implies_memOwn)))) h hp
  xperm_hyp hp2

/-- `account_extract_nonce_tail_spec_within` with the `x5` pin released to
    `regOwn` — the form the field-0 `rlp_walk_next`'s `regOwn` post feeds. -/
theorem account_extract_nonce_tail_own_spec_within
    (listBase outPtr raVal s0Old spF x1Val outMid : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin (7 * (Nat.toBytesBE a.nonce).length + 23)
      (extractNonceBase + 36) (raVal &&& ~~~1) accountExtractNonceFullCode
      (((.x10 ↦ᵣ (listBase + BitVec.ofNat 64
          (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x11 ↦ᵣ (0 : Word)) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        (.x1 ↦ᵣ x1Val) ** (.x2 ↦ᵣ spF) ** (.x8 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** bytesRegion listBase (encodeAccount a) ** (outPtr ↦ₘ outMid) **
        (spF ↦ₘ raVal) ** ((spF + 8) ↦ₘ s0Old)) **
        regOwn .x5)
      ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ (spF + 16)) ** (.x8 ↦ᵣ s0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase (encodeAccount a) **
        memOwn spF ** memOwn (spF + 8)) :=
  ownify1 (fun t0Old => account_extract_nonce_tail_spec_within listBase outPtr raVal
    s0Old spF x1Val outMid t0Old a hnonce hsalign hover hvalid)

/-! ## `account_extract_nonce`: the top-level triple -/

set_option maxRecDepth 8000 in
/-- **Top-level success triple for `account_extract_nonce`** (23-instruction
    body at its fixed guest address `GuestAddrs.account_extract_nonce`,
    composed with `rlp_walk_init`, `rlp_walk_next` and `rlp_content_to_u64`
    at theirs).

    From the accessor entry with `a0` = pointer to `encodeAccount a`, `a1` =
    its byte length, `a2` = a u64 output pointer, a stack pointer with two
    owned spill slots below it, and return address `raVal`, given the
    EIP-2681 bound `a.nonce < 2^64` the body deterministically returns to
    `raVal &&& ~~~1` with `a0 = 0` (success), the output cell holding
    `a.nonce`, callee-saved `s0`/`sp` and the input region preserved, and the
    stack slots returned to the caller. -/
theorem account_extract_nonce_spec_within
    (listBase outPtr spVal raVal s0Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (a : Account) (hnonce : a.nonce < 2 ^ 64)
    (hsalign : listBase.toNat % 8 = 0)
    (hover : listBase.toNat + (encodeAccount a).length < 2 ^ 64)
    (hvalid : ∀ k, k < (encodeAccount a).length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true) :
    cpsTripleWithin 139 extractNonceBase (raVal &&& ~~~1) accountExtractNonceFullCode
      ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) **
        (.x12 ↦ᵣ outPtr) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ spVal) ** (.x8 ↦ᵣ s0Old) **
        (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
        (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion listBase (encodeAccount a) ** memOwn outPtr **
        memOwn (spVal - 16) ** memOwn (spVal - 8))
      ((.x10 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (BitVec.ofNat 64 a.nonce)) **
        (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ spVal) ** (.x8 ↦ᵣ s0Old) ** (.x0 ↦ᵣ (0 : Word)) **
        regOwn .x11 ** regOwn .x12 ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        bytesRegion listBase (encodeAccount a) **
        memOwn (spVal - 16) ** memOwn (spVal - 8)) := by
  have hn256 : a.nonce < 2 ^ 256 := by
    have hle : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hlen70 : 70 ≤ (encodeAccount a).length := by
    rw [encodeAccount_length_eq a hn256]
    have := accountPayload_length_ge a
    omega
  have hvalid0 : isValidByteAccess listBase = true := by
    have h := hvalid 0 (by omega)
    rwa [show listBase + BitVec.ofNat 64 0 = listBase from by bv_omega] at h
  have hvalid1 : isValidByteAccess (listBase + 1) = true := by
    have h := hvalid 1 (by omega)
    rwa [show listBase + BitVec.ofNat 64 1 = listBase + 1 from by bv_omega] at h
  -- Prefix block idx 0..4 (`N → N+20`): allocate the stack frame, save
  -- `ra`/`s0`, set `s0 := outPtr`, zero the u64 output cell.
  have haddisp := addi_spec_gen_same_within .x2 spVal (-16 : BitVec 12) extractNonceBase
    (by decide)
  rw [show signExtend12 (-16 : BitVec 12) = (-16 : Word) from by decide,
      show spVal + (-16 : Word) = spVal - 16 from by bv_omega] at haddisp
  have hsd1 := sd_spec_gen_own_within .x2 .x1 (spVal - 16) raVal (0 : BitVec 12)
    (extractNonceBase + 4)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (spVal - 16) + (0 : Word) = spVal - 16 from by bv_omega] at hsd1
  have hsd2 := sd_spec_gen_own_within .x2 .x8 (spVal - 16) s0Old (8 : BitVec 12)
    (extractNonceBase + 8)
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
      show (spVal - 16) + (8 : Word) = spVal - 8 from by bv_omega] at hsd2
  have hmv8 := mv_spec_gen_within .x8 .x12 outPtr s0Old (extractNonceBase + 12) (by decide)
  have hsdo0 := sd_spec_gen_own_within .x8 .x0 outPtr (0 : Word) (0 : BitVec 12)
    (extractNonceBase + 16)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show outPtr + (0 : Word) = outPtr from by bv_omega] at hsdo0
  have hPrefix : cpsTripleWithin 5 extractNonceBase (extractNonceBase + 20)
      accountExtractNonceCode
      ((.x2 ↦ᵣ spVal) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ s0Old) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        memOwn (spVal - 16) ** memOwn (spVal - 8) ** memOwn outPtr)
      ((.x2 ↦ᵣ (spVal - 16)) ** (.x1 ↦ᵣ raVal) ** (.x8 ↦ᵣ outPtr) ** (.x12 ↦ᵣ outPtr) **
        (.x0 ↦ᵣ (0 : Word)) **
        ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) ** (outPtr ↦ₘ (0 : Word))) := by
    runBlock haddisp hsd1 hsd2 hmv8 hsdo0
  have hPrefix' := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ listBase) ** (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
      bytesRegion listBase (encodeAccount a))
    (by pcFree) (cpsTripleWithin_extend_code aen_sub hPrefix)
  -- Call `rlp_walk_init` (idx 5, `+20 → +24`).
  have hoffsetWI : (extractNonceBase + 20) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
        (Codegen.GuestAddrs.account_extract_nonce + 20)) = walkInitBase := by decide
  have halignWI : (extractNonceBase + 20 + 4) &&& ~~~(1 : Word) =
      extractNonceBase + 20 + 4 := by decide
  have hdisjWI : (CodeReq.singleton (extractNonceBase + 20)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
        (Codegen.GuestAddrs.account_extract_nonce + 20)))).Disjoint
      (rlp_walk_init_code walkInitBase) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len walkInitBase rlp_walk_init_prog 53 _
        rlp_walk_init_prog_length
        (fun k hk => by unfold extractNonceBase walkInitBase; bv_omega))
  have hWIcallee := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (spVal - 16)) ** (.x8 ↦ᵣ outPtr) **
      ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) ** (outPtr ↦ₘ (0 : Word)))
    (by pcFree)
    (account_rlp_walk_init_spec_within walkInitBase listBase (extractNonceBase + 20 + 4)
      outPtr t0Old t1Old t2Old t3Old t4Old t5Old t6Old a hn256 hsalign hover hvalid0 hvalid1)
  have hPrestWI : (((.x10 ↦ᵣ listBase) **
      (.x11 ↦ᵣ (BitVec.ofNat 64 (encodeAccount a).length)) ** (.x12 ↦ᵣ outPtr) **
      (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) ** (.x28 ↦ᵣ t3Old) **
      (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a)) **
      ((.x2 ↦ᵣ (spVal - 16)) ** (.x8 ↦ᵣ outPtr) **
        ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) **
        (outPtr ↦ₘ (0 : Word)))).pcFree := by pcFree
  have hcallWI := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
      (Codegen.GuestAddrs.account_extract_nonce + 20))
    (vOld := raVal) hoffsetWI halignWI hPrestWI hdisjWI
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hWIcallee)
  have hmonoWI : ∀ a' i,
      ((CodeReq.singleton (extractNonceBase + 20)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_init
          (Codegen.GuestAddrs.account_extract_nonce + 20)))).union
        (rlp_walk_init_code walkInitBase)) a' = some i →
      accountExtractNonceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aen_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 5
          (extractNonceBase + 20) (by decide) (by decide) (by decide)) a' i h))
      aen_wi_sub
  have hCallWI := cpsTripleWithin_extend_code hmonoWI hcallWI
  rw [show (extractNonceBase + 20 + 4 : Word) = extractNonceBase + 24 from by decide]
    at hCallWI
  -- BNE x12 x0 (idx 6, `+24 → +28`): not taken (walk_init status 0).
  have hbne6 := bne_spec_gen_within .x12 .x0 (44 : BitVec 13) (0 : Word) (0 : Word)
    (extractNonceBase + 24)
  rw [show (extractNonceBase + 24) + signExtend13 (44 : BitVec 13)
        = extractNonceBase + 68 from by decide,
      show (extractNonceBase + 24 : Word) + 4 = extractNonceBase + 28 from by decide]
    at hbne6
  have hmono6 : ∀ a' i, CodeReq.singleton (extractNonceBase + 24)
      (.BNE .x12 .x0 (44 : BitVec 13)) a' = some i →
      accountExtractNonceFullCode a' = some i :=
    fun a' i h => aen_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 6
        (extractNonceBase + 24) (by decide) (by decide) (by decide)) a' i h)
  have hBne6 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono6 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase + 2)) **
        (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        regOwn .x30 ** regOwn .x31 ** (.x1 ↦ᵣ (extractNonceBase + 24)) **
        bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ (spVal - 16)) ** (.x8 ↦ᵣ outPtr) **
        ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) ** (outPtr ↦ₘ (0 : Word)))
      (by pcFree) hbne6))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- Call `rlp_walk_next` for field 0 (idx 7, `+28 → +32`).
  have hoffsetW0 : (extractNonceBase + 28) + signExtend21
      (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
        (Codegen.GuestAddrs.account_extract_nonce + 28)) = walkNextBase := by decide
  have halignW0 : (extractNonceBase + 28 + 4) &&& ~~~(1 : Word) =
      extractNonceBase + 28 + 4 := by decide
  have hdisjW0 : (CodeReq.singleton (extractNonceBase + 28)
      (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
        (Codegen.GuestAddrs.account_extract_nonce + 28)))).Disjoint
      (rlp_walk_next_code walkNextBase) :=
    CodeReq.Disjoint.singleton_ofProg
      (CodeReq.ofProg_none_range_len walkNextBase rlp_walk_next_prog 103 _
        rlp_walk_next_prog_length
        (fun k hk => by unfold extractNonceBase walkNextBase; bv_omega))
  have hW0callee := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (spVal - 16)) ** (.x8 ↦ᵣ outPtr) ** regOwn .x30 ** regOwn .x31 **
      ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) ** (outPtr ↦ₘ (0 : Word)))
    (by pcFree)
    (account_rlp_walk_next_field0_own_spec_within walkNextBase listBase
      (extractNonceBase + 28 + 4) (0 : Word) a hn256 hsalign hover hvalid)
  have hPrestW0 : ((((.x10 ↦ᵣ (listBase + 2)) **
      (.x11 ↦ᵣ (listBase + BitVec.ofNat 64 (encodeAccount a).length)) **
      (.x12 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
      bytesRegion listBase (encodeAccount a)) **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29) **
      ((.x2 ↦ᵣ (spVal - 16)) ** (.x8 ↦ᵣ outPtr) ** regOwn .x30 ** regOwn .x31 **
        ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) **
        (outPtr ↦ₘ (0 : Word)))).pcFree := by pcFree
  have hcallW0 := WP.cpsCallWithin
    (offset := Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
      (Codegen.GuestAddrs.account_extract_nonce + 28))
    (vOld := extractNonceBase + 24) hoffsetW0 halignW0 hPrestW0 hdisjW0
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => hp) hW0callee)
  have hmonoW0 : ∀ a' i,
      ((CodeReq.singleton (extractNonceBase + 28)
        (.JAL .x1 (Codegen.jalOff Codegen.GuestAddrs.rlp_walk_next
          (Codegen.GuestAddrs.account_extract_nonce + 28)))).union
        (rlp_walk_next_code walkNextBase)) a' = some i →
      accountExtractNonceFullCode a' = some i :=
    CodeReq.union_split_mono
      (fun a' i h => aen_sub a' i (CodeReq.singleton_mono
        (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 7
          (extractNonceBase + 28) (by decide) (by decide) (by decide)) a' i h))
      aen_wn_sub
  have hCallW0 := cpsTripleWithin_extend_code hmonoW0 hcallW0
  rw [show (extractNonceBase + 28 + 4 : Word) = extractNonceBase + 32 from by decide]
    at hCallW0
  -- BNE x11 x0 (idx 8, `+32 → +36`): not taken (walk_next status 0).
  have hbne8 := bne_spec_gen_within .x11 .x0 (36 : BitVec 13) (0 : Word) (0 : Word)
    (extractNonceBase + 32)
  rw [show (extractNonceBase + 32) + signExtend13 (36 : BitVec 13)
        = extractNonceBase + 68 from by decide,
      show (extractNonceBase + 32 : Word) + 4 = extractNonceBase + 36 from by decide]
    at hbne8
  have hmono8 : ∀ a' i, CodeReq.singleton (extractNonceBase + 32)
      (.BNE .x11 .x0 (36 : BitVec 13)) a' = some i →
      accountExtractNonceFullCode a' = some i :=
    fun a' i h => aen_sub a' i (CodeReq.singleton_mono
      (CodeReq.ofProg_lookup_addr extractNonceBase Codegen.accountExtractNonce_prog 8
        (extractNonceBase + 32) (by decide) (by decide) (by decide)) a' i h)
  have hBne8 := cpsBranchWithin_ntakenPath
    (cpsBranchWithin_extend_code hmono8 (cpsBranchWithin_frameR
      ((.x10 ↦ᵣ (listBase +
          BitVec.ofNat 64 (2 + (encodeBytes (Nat.toBytesBE a.nonce)).length))) **
        (.x12 ↦ᵣ (BitVec.ofNat 64 (Nat.toBytesBE a.nonce).length)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
        (.x1 ↦ᵣ (extractNonceBase + 32)) ** bytesRegion listBase (encodeAccount a) **
        (.x2 ↦ᵣ (spVal - 16)) ** (.x8 ↦ᵣ outPtr) ** regOwn .x30 ** regOwn .x31 **
        ((spVal - 16) ↦ₘ raVal) ** ((spVal - 8) ↦ₘ s0Old) ** (outPtr ↦ₘ (0 : Word)))
      (by pcFree) hbne8))
    (fun hp hQt => by
      obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
      exact ((sepConj_pure_right _).1 h_pure).2 rfl)
  -- The verified tail from `+36`.
  have hTail := account_extract_nonce_tail_own_spec_within listBase outPtr raVal s0Old
    (spVal - 16) (extractNonceBase + 32) (0 : Word) a hnonce hsalign hover hvalid
  rw [show ((spVal - 16 : Word) + 8) = spVal - 8 from by bv_omega,
      show ((spVal - 16 : Word) + 16) = spVal from by bv_omega] at hTail
  -- Compose the whole chain.
  have t1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hPrefix' hCallWI; intro h hp; xperm_hyp hp
  have t2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t1 hBne6; intro h hp; xperm_hyp hp
  have t3 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t2 hCallW0
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have t4 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t3 hBne8; intro h hp; xperm_hyp hp
  have t5 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ t4 hTail
    intro h hp
    have hp2 := sepConj_mono_left (sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
    xperm_hyp hp2
  have hcn8 : (Nat.toBytesBE a.nonce).length ≤ 8 := account_nonce_field_len_le_8 a hnonce
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) t5)

end EvmAsm.Codegen
