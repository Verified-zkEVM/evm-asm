/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashUnified

  Unified whole-routine contract for `header_validate_parent_hash`
  (conjunct 11 of `validate_header`): the caller-visible outcome is a
  THREE-WAY disjunction in the POST (no outcome guards in the pre), with the
  status-2 arm stating "first differing dword k" for ANY k < 4 - closing the
  dword-1/2/3 coverage gap of the landed per-arm adapters (a unified claim
  over only the round-0 arms would have been FALSE, not incomplete).

  Composition insight: the landed match/mismatch adapters pin the entry
  Claimed-cell content to the post-extraction bytes (claimedBytes =
  claimedOut), which only covers inputs where the leaf writes back identical
  bytes.  Here the entry content is an arbitrary `C0`; the leaf
  `headers_parent_hash` OVERWRITES the cell with
  `headersParentHash_out thisBytes C0` before the compare phase, so the
  keccak arms compose `hvphPrologueHeaders` (C0 -> out) DIRECTLY with
  `hvphFromHeadersMatch` / `hvphFromHeadersMismatch{k}` instantiated at
  `claimedBytes := out`.  The extract-fail arm reuses the landed
  `header_validate_parent_hash_extract_fail_spec_within` adapter, which
  already carries distinct claimedBytes/claimedOut binders.

  Cost: the theorem's step count is a single static UPPER BOUND
  `40 + 312 + nKeccak N rem` (match arm's exact cost, which dominates:
  extract-fail 19 + 312; mismatch_k 30 + 312 + nK + 3*k <= 39 + 312 + nK);
  each arm is lifted with `cpsTripleWithin_mono_nSteps`.

  Static premises: the leaf premises (hlenW/hlen3/hclaim0/hsalign/hsover/
  hsvalid) are facts about the caller-owned exact RLP window and pointer,
  established at the `validate_header` envelope; the keccak envelope
  constrains only the PARENT buffer, the `zk3_state` scratch arena and the
  keccak cursor (allocation/alignment/arithmetic), never the content of
  `thisBytes`, so extract-fail inputs satisfy it as well.  `hOutLen` is the
  extraction length fact (from the leaf's field-0 extraction spec on the
  status-0 path).
-/

import EvmAsm.Codegen.Programs.HeaderValidateParentHashMatch
import EvmAsm.Codegen.Programs.HeaderValidateParentHashMismatchLate
import EvmAsm.Codegen.Programs.HeaderValidateParentHashExtractFail
import EvmAsm.Codegen.Programs.HeadersParentHashMain

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

/-! ## Leaf discharge: `headersCallPremise` from `headers_parent_hash_spec_within` -/

/-- The composition residual `h_headers` discharged from the proven leaf.
    The leaf overwrites the Claimed cell with `headersParentHash_out`, so
    this works for ANY entry content `C0` and ANY symbolic status. -/
theorem hvph_headersCallPremise_of_leaf
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (thisBytes C0 parentBytes : List (BitVec 8))
    (_hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k < thisBytes.length,
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) :
    headersCallPremise 312 (H + 40) (headersParentHash_status thisBytes)
      thisPtr thisLen thisBytes C0 (headersParentHash_out thisBytes C0)
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
  unfold headersCallPremise
  -- `(GuestAddrs.headers_parent_hash : Word)` is `hphBase` and `headersProg`
  -- is `headersParentHash_prog`, so the goal's code/base are the leaf's.
  have hret40 : (H + 40) &&& ~~~(1 : Word) = (H + 40) := by decide
  have hleaf : ∀ v5 v6 v7 v28,
      cpsTripleWithin 312 hphBase (H + 40) hphCode
        ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ Claimed) **
          (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          claimedOwn C0 **
          bytesRegion thisPtr thisBytes **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
        ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ headersParentHash_status thisBytes) **
          regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
          claimedOwn (headersParentHash_out thisBytes C0) **
          bytesRegion thisPtr thisBytes ** regOwn .x11 ** regOwn .x12 **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) := by
    intro v5 v6 v7 v28
    exact EvmAsm.Codegen.headers_parent_hash_spec_within (H + 40)
      thisPtr thisLen v5 v6 v7 v28 thisBytes C0
      ((.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
        (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)))
      (by
        repeat'
          first
          | apply pcFree_sepConj
          | exact pcFree_regIs
          | exact pcFree_regOwn
          | exact pcFree_memIs
          | exact bytesRegion_pcFree _ _
          | exact pcFree_frameSlotsOwn _ _
          | exact pcFree_emp)
      hret40 hlenW hlen3 hclaim0 hsalign hsover hsvalid
  -- Convert the four scratch pins to `regOwn`, mirroring the landed
  -- `hvphFromCompareSetupMismatch0` wrapper: lemma on the tail pair, a
  -- permuting weaken to bring the next pair to the tail, lemma again, then
  -- bridge the leaf by permutation.
  have hA : cpsTripleWithin 312 hphBase (H + 40) hphCode
      ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ Claimed) ** claimedOwn C0 **
          bytesRegion thisPtr thisBytes **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) **
        regOwn .x5 ** regOwn .x6) **
      regOwn .x7 ** regOwn .x28)
      ((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ headersParentHash_status thisBytes) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        claimedOwn (headersParentHash_out thisBytes C0) **
        bytesRegion thisPtr thisBytes ** regOwn .x11 ** regOwn .x12 **
        (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
        (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        bytesRegion parentPtr parentBytes **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word))) := by
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x7) (r2 := .x28)
      (fun v7 v28 => ?_)
    refine cpsTripleWithin_weaken
      (P := ((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
          (.x12 ↦ᵣ Claimed) ** claimedOwn C0 **
          bytesRegion thisPtr thisBytes **
          (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
          (.x18 ↦ᵣ vals .x18) ** (.x13 ↦ᵣ parentLen) **
          frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
          bytesRegion parentPtr parentBytes **
          regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
          (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
        regOwn .x5 ** regOwn .x6)))
      (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
    refine cpsTripleWithin_of_forall_regIs_to_regOwn2 (r1 := .x5) (r2 := .x6)
      (fun v5 v6 => ?_)
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
      (hleaf v5 v6 v7 v28)
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hA
  · unfold headersCallFrame claimedOwn at hp
    xperm_hyp hp
  · unfold headersCallFrame claimedOwn
    xperm_hyp hq

/-! ## Unified per-outcome arms (adapter shape, arbitrary entry Claimed content)

    Each arm composes `hvphPrologueHeaders` (with the leaf discharged via
    `hvph_headersCallPremise_of_leaf`, so the Claimed cell content moves from
    the entry `C0` to `headersParentHash_out thisBytes C0`) directly with the
    landed `hvphFromHeaders*` mid pieces instantiated at the EXTRACTED bytes.
    The landed adapter levels re-pin `claimedBytes = claimedOut` and so cannot
    express the arbitrary-`C0` entry; these arms are the bridge. -/

set_option maxRecDepth 8000 in
/-- Status-0 (match) whole-routine arm: extraction succeeds, the one-shot
    keccak computes the parent digest, and all four compare dwords agree. -/
theorem hvphUnifiedMatch
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hst0 : headersParentHash_status thisBytes = (0 : Word))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
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
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (h0 : dwordAt (headersParentHash_out thisBytes C0) 0 =
      dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt (headersParentHash_out thisBytes C0) 1 =
      dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt (headersParentHash_out thisBytes C0) 2 =
      dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h3 : dwordAt (headersParentHash_out thisBytes C0) 3 =
      dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (40 + 312 + nKeccak N rem) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (0 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
          (headersParentHash_out thisBytes C0) digest N rem F) := by
  intro digest out0 Amb
  have h0headers : headersCallPremise 312 (H + 40) (0 : Word) thisPtr thisLen
      thisBytes C0 (headersParentHash_out thisBytes C0)
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    have h := hvph_headersCallPremise_of_leaf sp0 spC ret thisPtr thisLen
      parentPtr parentLen vals thisBytes C0 parentBytes hspC hlenW hlen3 hclaim0
      hsalign hsover hsvalid
    rw [hst0] at h
    exact h
  have hint : cpsTripleWithin (40 + 312 + nKeccak N rem) H
      (hvphFrameVals ret vals .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn C0 **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (0 : Word)) ** (.x1 ↦ᵣ (hvphFrameVals ret vals) .x1) **
        (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ (hvphFrameVals ret vals) .x8) **
        (.x9 ↦ᵣ (hvphFrameVals ret vals) .x9) **
        (.x18 ↦ᵣ (hvphFrameVals ret vals) .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt (headersParentHash_out thisBytes C0) 3) **
        (.x28 ↦ᵣ dwordAt digest 3) **
        claimedOwn (headersParentHash_out thisBytes C0) **
        bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
    have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
    have hph0 := hvphPrologueHeaders 312 sp0 spC ret thisPtr thisLen parentPtr
      parentLen (0 : Word) vals thisBytes parentBytes C0
      (headersParentHash_out thisBytes C0) hspC h0headers
    have hph := cpsTripleWithin_frameR Amb hAmb hph0
    have hmatch := hvphFromHeadersMatch sp0 spC ret parentPtr parentLen vals
      v20 parentBytes (headersParentHash_out thisBytes C0) N rem os thisPtr
      thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hOutLen h0 h1 h2 h3
    -- Bridge PrologueHeaders.post ** Amb → FromHeadersMatch.pre (demote x13; peel owns).
    have hphW :=
      cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
        unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
        let Rest : Assertion :=
          (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn (headersParentHash_out thisBytes C0) **
            bytesRegion thisPtr thisBytes **
            (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
            (.x18 ↦ᵣ vals .x18) **
            frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
            bytesRegion parentPtr parentBytes **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x30 ** regOwn .x31 **
            (.x20 ↦ᵣ v20) ** stackFree spC 4 **
            regOwns [.x14, .x15, .x16, .x17] **
            bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
            bytesRegion Computed out0 ** F **
            regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
        have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
          simp only [Rest]
          xperm_hyp hq
        have hqOwn : (Rest ** regOwn .x13) s :=
          sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
        change
          (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                claimedOwn (headersParentHash_out thisBytes C0) **
                headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
                hvphSuccKeccakAmb spC v20 os out0
                  (bytesRegion thisPtr thisBytes ** F)) **
              regOwn .x11 ** regOwn .x12) **
            regOwn .x28 ** regOwn .x29) s)
        · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
          simp only [Rest] at hqOwn
          xperm_hyp hqOwn) hph
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [out0] at hp ⊢
      xperm_hyp hp) hphW hmatch
    have hn : (9 + (1 + 312)) + (30 + nKeccak N rem)
        = 40 + 312 + nKeccak N rem := by omega
    rw [← hn]
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      xperm_hyp hq) hall
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hint
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using hvphKeccakExit_post_to_adapter sp0 spC ret
      parentPtr parentLen v20 (0 : Word)
      (dwordAt (headersParentHash_out thisBytes C0) 3)
      (dwordAt (keccakBodyDigest parentBytes N rem) 3) vals thisPtr thisBytes
      parentBytes (headersParentHash_out thisBytes C0) N rem F hspC hlen s hq

set_option maxRecDepth 8000 in
/-- Status-2 (hash mismatch) whole-routine arm: extraction succeeds and
    the first differing compare dword is round 0. -/
theorem hvphUnifiedMismatch0
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hst0 : headersParentHash_status thisBytes = (0 : Word))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
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
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (h_ne : dwordAt (headersParentHash_out thisBytes C0) 0 ≠
      dwordAt (keccakBodyDigest parentBytes N rem) 0) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 0) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
          (headersParentHash_out thisBytes C0) digest N rem F) := by
  intro digest out0 Amb
  have h0headers : headersCallPremise 312 (H + 40) (0 : Word) thisPtr thisLen
      thisBytes C0 (headersParentHash_out thisBytes C0)
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    have h := hvph_headersCallPremise_of_leaf sp0 spC ret thisPtr thisLen
      parentPtr parentLen vals thisBytes C0 parentBytes hspC hlenW hlen3 hclaim0
      hsalign hsover hsvalid
    rw [hst0] at h
    exact h
  have hint : cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 0) H
      (hvphFrameVals ret vals .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn C0 **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ (hvphFrameVals ret vals) .x1) **
        (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ (hvphFrameVals ret vals) .x8) **
        (.x9 ↦ᵣ (hvphFrameVals ret vals) .x9) **
        (.x18 ↦ᵣ (hvphFrameVals ret vals) .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt (headersParentHash_out thisBytes C0) 0) **
        (.x28 ↦ᵣ dwordAt digest 0) **
        claimedOwn (headersParentHash_out thisBytes C0) **
        bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
    have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
    have hph0 := hvphPrologueHeaders 312 sp0 spC ret thisPtr thisLen parentPtr
      parentLen (0 : Word) vals thisBytes parentBytes C0
      (headersParentHash_out thisBytes C0) hspC h0headers
    have hph := cpsTripleWithin_frameR Amb hAmb hph0
    have hmatch := hvphFromHeadersMismatch0 sp0 spC ret parentPtr parentLen vals
      v20 parentBytes (headersParentHash_out thisBytes C0) N rem os thisPtr
      thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hOutLen h_ne
    -- Bridge PrologueHeaders.post ** Amb → FromHeadersMatch.pre (demote x13; peel owns).
    have hphW :=
      cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
        unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
        let Rest : Assertion :=
          (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn (headersParentHash_out thisBytes C0) **
            bytesRegion thisPtr thisBytes **
            (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
            (.x18 ↦ᵣ vals .x18) **
            frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
            bytesRegion parentPtr parentBytes **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x30 ** regOwn .x31 **
            (.x20 ↦ᵣ v20) ** stackFree spC 4 **
            regOwns [.x14, .x15, .x16, .x17] **
            bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
            bytesRegion Computed out0 ** F **
            regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
        have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
          simp only [Rest]
          xperm_hyp hq
        have hqOwn : (Rest ** regOwn .x13) s :=
          sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
        change
          (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                claimedOwn (headersParentHash_out thisBytes C0) **
                headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
                hvphSuccKeccakAmb spC v20 os out0
                  (bytesRegion thisPtr thisBytes ** F)) **
              regOwn .x11 ** regOwn .x12) **
            regOwn .x28 ** regOwn .x29) s)
        · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
          simp only [Rest] at hqOwn
          xperm_hyp hqOwn) hph
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [out0] at hp ⊢
      xperm_hyp hp) hphW hmatch
    have hn : (9 + (1 + 312)) + (20 + 3 * 0 + nKeccak N rem)
        = 30 + 312 + nKeccak N rem + 3 * 0 := by omega
    rw [← hn]
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      xperm_hyp hq) hall
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hint
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using hvphKeccakExit_post_to_adapter sp0 spC ret
      parentPtr parentLen v20 (2 : Word)
      (dwordAt (headersParentHash_out thisBytes C0) 0)
      (dwordAt (keccakBodyDigest parentBytes N rem) 0) vals thisPtr thisBytes
      parentBytes (headersParentHash_out thisBytes C0) N rem F hspC hlen s hq

set_option maxRecDepth 8000 in
/-- Status-2 (hash mismatch) whole-routine arm: extraction succeeds and
    the first differing compare dword is round 1. -/
theorem hvphUnifiedMismatch1
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hst0 : headersParentHash_status thisBytes = (0 : Word))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
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
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (h0 : dwordAt (headersParentHash_out thisBytes C0) 0 =
      dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h_ne : dwordAt (headersParentHash_out thisBytes C0) 1 ≠
      dwordAt (keccakBodyDigest parentBytes N rem) 1) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 1) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
          (headersParentHash_out thisBytes C0) digest N rem F) := by
  intro digest out0 Amb
  have h0headers : headersCallPremise 312 (H + 40) (0 : Word) thisPtr thisLen
      thisBytes C0 (headersParentHash_out thisBytes C0)
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    have h := hvph_headersCallPremise_of_leaf sp0 spC ret thisPtr thisLen
      parentPtr parentLen vals thisBytes C0 parentBytes hspC hlenW hlen3 hclaim0
      hsalign hsover hsvalid
    rw [hst0] at h
    exact h
  have hint : cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 1) H
      (hvphFrameVals ret vals .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn C0 **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ (hvphFrameVals ret vals) .x1) **
        (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ (hvphFrameVals ret vals) .x8) **
        (.x9 ↦ᵣ (hvphFrameVals ret vals) .x9) **
        (.x18 ↦ᵣ (hvphFrameVals ret vals) .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt (headersParentHash_out thisBytes C0) 1) **
        (.x28 ↦ᵣ dwordAt digest 1) **
        claimedOwn (headersParentHash_out thisBytes C0) **
        bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
    have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
    have hph0 := hvphPrologueHeaders 312 sp0 spC ret thisPtr thisLen parentPtr
      parentLen (0 : Word) vals thisBytes parentBytes C0
      (headersParentHash_out thisBytes C0) hspC h0headers
    have hph := cpsTripleWithin_frameR Amb hAmb hph0
    have hmatch := hvphFromHeadersMismatch1 sp0 spC ret parentPtr parentLen vals
      v20 parentBytes (headersParentHash_out thisBytes C0) N rem os thisPtr
      thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hOutLen h0 h_ne
    -- Bridge PrologueHeaders.post ** Amb → FromHeadersMatch.pre (demote x13; peel owns).
    have hphW :=
      cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
        unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
        let Rest : Assertion :=
          (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn (headersParentHash_out thisBytes C0) **
            bytesRegion thisPtr thisBytes **
            (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
            (.x18 ↦ᵣ vals .x18) **
            frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
            bytesRegion parentPtr parentBytes **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x30 ** regOwn .x31 **
            (.x20 ↦ᵣ v20) ** stackFree spC 4 **
            regOwns [.x14, .x15, .x16, .x17] **
            bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
            bytesRegion Computed out0 ** F **
            regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
        have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
          simp only [Rest]
          xperm_hyp hq
        have hqOwn : (Rest ** regOwn .x13) s :=
          sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
        change
          (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                claimedOwn (headersParentHash_out thisBytes C0) **
                headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
                hvphSuccKeccakAmb spC v20 os out0
                  (bytesRegion thisPtr thisBytes ** F)) **
              regOwn .x11 ** regOwn .x12) **
            regOwn .x28 ** regOwn .x29) s)
        · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
          simp only [Rest] at hqOwn
          xperm_hyp hqOwn) hph
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [out0] at hp ⊢
      xperm_hyp hp) hphW hmatch
    have hn : (9 + (1 + 312)) + (20 + 3 * 1 + nKeccak N rem)
        = 30 + 312 + nKeccak N rem + 3 * 1 := by omega
    rw [← hn]
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      xperm_hyp hq) hall
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hint
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using hvphKeccakExit_post_to_adapter sp0 spC ret
      parentPtr parentLen v20 (2 : Word)
      (dwordAt (headersParentHash_out thisBytes C0) 1)
      (dwordAt (keccakBodyDigest parentBytes N rem) 1) vals thisPtr thisBytes
      parentBytes (headersParentHash_out thisBytes C0) N rem F hspC hlen s hq

set_option maxRecDepth 8000 in
/-- Status-2 (hash mismatch) whole-routine arm: extraction succeeds and
    the first differing compare dword is round 2. -/
theorem hvphUnifiedMismatch2
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hst0 : headersParentHash_status thisBytes = (0 : Word))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
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
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (h0 : dwordAt (headersParentHash_out thisBytes C0) 0 =
      dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt (headersParentHash_out thisBytes C0) 1 =
      dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h_ne : dwordAt (headersParentHash_out thisBytes C0) 2 ≠
      dwordAt (keccakBodyDigest parentBytes N rem) 2) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 2) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
          (headersParentHash_out thisBytes C0) digest N rem F) := by
  intro digest out0 Amb
  have h0headers : headersCallPremise 312 (H + 40) (0 : Word) thisPtr thisLen
      thisBytes C0 (headersParentHash_out thisBytes C0)
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    have h := hvph_headersCallPremise_of_leaf sp0 spC ret thisPtr thisLen
      parentPtr parentLen vals thisBytes C0 parentBytes hspC hlenW hlen3 hclaim0
      hsalign hsover hsvalid
    rw [hst0] at h
    exact h
  have hint : cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 2) H
      (hvphFrameVals ret vals .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn C0 **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ (hvphFrameVals ret vals) .x1) **
        (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ (hvphFrameVals ret vals) .x8) **
        (.x9 ↦ᵣ (hvphFrameVals ret vals) .x9) **
        (.x18 ↦ᵣ (hvphFrameVals ret vals) .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt (headersParentHash_out thisBytes C0) 2) **
        (.x28 ↦ᵣ dwordAt digest 2) **
        claimedOwn (headersParentHash_out thisBytes C0) **
        bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
    have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
    have hph0 := hvphPrologueHeaders 312 sp0 spC ret thisPtr thisLen parentPtr
      parentLen (0 : Word) vals thisBytes parentBytes C0
      (headersParentHash_out thisBytes C0) hspC h0headers
    have hph := cpsTripleWithin_frameR Amb hAmb hph0
    have hmatch := hvphFromHeadersMismatch2 sp0 spC ret parentPtr parentLen vals
      v20 parentBytes (headersParentHash_out thisBytes C0) N rem os thisPtr
      thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hOutLen h0 h1 h_ne
    -- Bridge PrologueHeaders.post ** Amb → FromHeadersMatch.pre (demote x13; peel owns).
    have hphW :=
      cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
        unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
        let Rest : Assertion :=
          (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn (headersParentHash_out thisBytes C0) **
            bytesRegion thisPtr thisBytes **
            (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
            (.x18 ↦ᵣ vals .x18) **
            frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
            bytesRegion parentPtr parentBytes **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x30 ** regOwn .x31 **
            (.x20 ↦ᵣ v20) ** stackFree spC 4 **
            regOwns [.x14, .x15, .x16, .x17] **
            bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
            bytesRegion Computed out0 ** F **
            regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
        have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
          simp only [Rest]
          xperm_hyp hq
        have hqOwn : (Rest ** regOwn .x13) s :=
          sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
        change
          (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                claimedOwn (headersParentHash_out thisBytes C0) **
                headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
                hvphSuccKeccakAmb spC v20 os out0
                  (bytesRegion thisPtr thisBytes ** F)) **
              regOwn .x11 ** regOwn .x12) **
            regOwn .x28 ** regOwn .x29) s)
        · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
          simp only [Rest] at hqOwn
          xperm_hyp hqOwn) hph
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [out0] at hp ⊢
      xperm_hyp hp) hphW hmatch
    have hn : (9 + (1 + 312)) + (20 + 3 * 2 + nKeccak N rem)
        = 30 + 312 + nKeccak N rem + 3 * 2 := by omega
    rw [← hn]
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      xperm_hyp hq) hall
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hint
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using hvphKeccakExit_post_to_adapter sp0 spC ret
      parentPtr parentLen v20 (2 : Word)
      (dwordAt (headersParentHash_out thisBytes C0) 2)
      (dwordAt (keccakBodyDigest parentBytes N rem) 2) vals thisPtr thisBytes
      parentBytes (headersParentHash_out thisBytes C0) N rem F hspC hlen s hq

set_option maxRecDepth 8000 in
/-- Status-2 (hash mismatch) whole-routine arm: extraction succeeds and
    the first differing compare dword is round 3. -/
theorem hvphUnifiedMismatch3
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hst0 : headersParentHash_status thisBytes = (0 : Word))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
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
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true)
    (h0 : dwordAt (headersParentHash_out thisBytes C0) 0 =
      dwordAt (keccakBodyDigest parentBytes N rem) 0)
    (h1 : dwordAt (headersParentHash_out thisBytes C0) 1 =
      dwordAt (keccakBodyDigest parentBytes N rem) 1)
    (h2 : dwordAt (headersParentHash_out thisBytes C0) 2 =
      dwordAt (keccakBodyDigest parentBytes N rem) 2)
    (h_ne : dwordAt (headersParentHash_out thisBytes C0) 3 ≠
      dwordAt (keccakBodyDigest parentBytes N rem) 3) :
    let digest := keccakBodyDigest parentBytes N rem
    let out0 := List.replicate 32 (0 : BitVec 8)
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 3) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** Amb)
      (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
        hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
          (headersParentHash_out thisBytes C0) digest N rem F) := by
  intro digest out0 Amb
  have h0headers : headersCallPremise 312 (H + 40) (0 : Word) thisPtr thisLen
      thisBytes C0 (headersParentHash_out thisBytes C0)
      (headersCallFrame spC ret parentPtr parentLen vals parentBytes) := by
    have h := hvph_headersCallPremise_of_leaf sp0 spC ret thisPtr thisLen
      parentPtr parentLen vals thisBytes C0 parentBytes hspC hlenW hlen3 hclaim0
      hsalign hsover hsvalid
    rw [hst0] at h
    exact h
  have hint : cpsTripleWithin (30 + 312 + nKeccak N rem + 3 * 3) H
      (hvphFrameVals ret vals .x1) fullCode
      ((.x2 ↦ᵣ sp0) ** regsAt hvphFrame (hvphFrameVals ret vals) **
        frameSlotsOwn hvphFrame spC **
        (.x10 ↦ᵣ thisPtr) ** (.x11 ↦ᵣ thisLen) **
        (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ parentLen) **
        claimedOwn C0 **
        bytesRegion thisPtr thisBytes ** bytesRegion parentPtr parentBytes **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) **
        Amb)
      ((.x10 ↦ᵣ (2 : Word)) ** (.x1 ↦ᵣ (hvphFrameVals ret vals) .x1) **
        (.x2 ↦ᵣ sp0) **
        (.x8 ↦ᵣ (hvphFrameVals ret vals) .x8) **
        (.x9 ↦ᵣ (hvphFrameVals ret vals) .x9) **
        (.x18 ↦ᵣ (hvphFrameVals ret vals) .x18) **
        frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
        (.x5 ↦ᵣ Claimed) ** (.x6 ↦ᵣ Computed) **
        (.x7 ↦ᵣ dwordAt (headersParentHash_out thisBytes C0) 3) **
        (.x28 ↦ᵣ dwordAt digest 3) **
        claimedOwn (headersParentHash_out thisBytes C0) **
        bytesRegion Computed digest **
        (frameSlotsSaved keccakFrame (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals parentPtr parentLen (vals .x18) v20) **
          (.x20 ↦ᵣ v20) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad parentBytes N rem) rem) 0)) **
          (.x0 ↦ᵣ (0 : Word)) **
          regOwns [.x29, .x30, .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          keccakCallerFreeA parentPtr parentBytes N empAssertion **
          bytesRegion thisPtr thisBytes ** F)) := by
    have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
    have hph0 := hvphPrologueHeaders 312 sp0 spC ret thisPtr thisLen parentPtr
      parentLen (0 : Word) vals thisBytes parentBytes C0
      (headersParentHash_out thisBytes C0) hspC h0headers
    have hph := cpsTripleWithin_frameR Amb hAmb hph0
    have hmatch := hvphFromHeadersMismatch3 sp0 spC ret parentPtr parentLen vals
      v20 parentBytes (headersParentHash_out thisBytes C0) N rem os thisPtr
      thisBytes F hF hspC hret hplen hlen hrem_le hos
      halign_zk hover hNbound hrem64 hb8i
      hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
      hOutLen h0 h1 h2 h_ne
    -- Bridge PrologueHeaders.post ** Amb → FromHeadersMatch.pre (demote x13; peel owns).
    have hphW :=
      cpsTripleWithin_weaken (fun _ hp => hp) (fun s hq => by
        unfold headersCallFrame Amb hvphSuccKeccakAmb at hq
        let Rest : Assertion :=
          (.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
            claimedOwn (headersParentHash_out thisBytes C0) **
            bytesRegion thisPtr thisBytes **
            (.x2 ↦ᵣ spC) ** (.x8 ↦ᵣ parentPtr) ** (.x9 ↦ᵣ parentLen) **
            (.x18 ↦ᵣ vals .x18) **
            frameSlotsSaved hvphFrame spC (hvphFrameVals ret vals) **
            bytesRegion parentPtr parentBytes **
            regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
            regOwn .x30 ** regOwn .x31 **
            (.x20 ↦ᵣ v20) ** stackFree spC 4 **
            regOwns [.x14, .x15, .x16, .x17] **
            bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state) os **
            bytesRegion Computed out0 ** F **
            regOwn .x11 ** regOwn .x12 ** regOwn .x28 ** regOwn .x29
        have hqTrail : (Rest ** (.x13 ↦ᵣ parentLen)) s := by
          simp only [Rest]
          xperm_hyp hq
        have hqOwn : (Rest ** regOwn .x13) s :=
          sepConj_mono_right (regIs_to_regOwn .x13 parentLen) s hqTrail
        change
          (((((.x1 ↦ᵣ (H + 40)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
                claimedOwn (headersParentHash_out thisBytes C0) **
                headersCallFrameSuccCore spC ret parentPtr parentLen vals parentBytes **
                hvphSuccKeccakAmb spC v20 os out0
                  (bytesRegion thisPtr thisBytes ** F)) **
              regOwn .x11 ** regOwn .x12) **
            regOwn .x28 ** regOwn .x29) s)
        · unfold headersCallFrameSuccCore hvphSuccKeccakAmb
          simp only [Rest] at hqOwn
          xperm_hyp hqOwn) hph
    have hall := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      simp only [out0] at hp ⊢
      xperm_hyp hp) hphW hmatch
    have hn : (9 + (1 + 312)) + (20 + 3 * 3 + nKeccak N rem)
        = 30 + 312 + nKeccak N rem + 3 * 3 := by omega
    rw [← hn]
    exact cpsTripleWithin_weaken (fun _ hp => by
      simp only [Amb] at hp ⊢
      xperm_hyp hp) (fun _ hq => by
      xperm_hyp hq) hall
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hint
  · unfold hvphPre at hp
    simp only [Amb, hvphSuccKeccakAmb, regsAt_hvphFrame_of_vals, hspC] at hp ⊢
    xperm_hyp hp
  · simpa [digest, Amb] using hvphKeccakExit_post_to_adapter sp0 spC ret
      parentPtr parentLen v20 (2 : Word)
      (dwordAt (headersParentHash_out thisBytes C0) 3)
      (dwordAt (keccakBodyDigest parentBytes N rem) 3) vals thisPtr thisBytes
      parentBytes (headersParentHash_out thisBytes C0) N rem F hspC hlen s hq

set_option maxRecDepth 8000 in
/-- The unified whole-routine contract for `header_validate_post_merge`'s
    sibling `header_validate_parent_hash` (K61, #12461 arm 11): one triple over
    the full closure with NO outcome guard in the pre; the three machine
    outcomes live in the post disjunction.  The step count is a single static
    UPPER BOUND (the match arm's exact cost, which dominates: extract-fail is
    19+312, mismatch-at-round-k is 30+312+nK+3k ≤ 39+312+nK). -/
theorem header_validate_parent_hash_spec_within
    (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word) (vals : Reg → Word)
    (v20 : Word)
    (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
    (os : List (BitVec 8))
    (F : Assertion) (hF : F.pcFree)
    (hret : ret &&& ~~~(1 : Word) = ret)
    (hspC : spC = sp0 + signExtend12 (-32 : BitVec 12))
    (hlenW : thisBytes.length = thisLen.toNat)
    (hlen3 : 3 ≤ thisBytes.length)
    (hclaim0 : C0.length = 32)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hOutLen : (headersParentHash_out thisBytes C0).length = 32)
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
    let Amb := hvphSuccKeccakAmb spC v20 os out0 F
    cpsTripleWithin (40 + 312 + nKeccak N rem) H ret fullCode
      ((.x1 ↦ᵣ ret) **
        hvphPre sp0 thisPtr thisLen parentPtr parentLen vals thisBytes parentBytes **
        claimedOwn C0 ** Amb)
      (fun s =>
        (⌜headersParentHash_status thisBytes = (0 : Word) ∧
            ∀ q, q < 4 → dwordAt (headersParentHash_out thisBytes C0) q =
              dwordAt (keccakBodyDigest parentBytes N rem) q⌝ **
          (hvphPost sp0 thisPtr parentPtr ret (0 : Word) vals thisBytes parentBytes **
            hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
              (headersParentHash_out thisBytes C0)
              (keccakBodyDigest parentBytes N rem) N rem F)) s ∨
        (⌜headersParentHash_status thisBytes ≠ (0 : Word)⌝ **
          ((hvphPost sp0 thisPtr parentPtr ret (1 : Word) vals thisBytes parentBytes **
            claimedOwn (headersParentHash_out thisBytes C0)) ** Amb)) s ∨
        ∃ k, k < 4 ∧
          (⌜headersParentHash_status thisBytes = (0 : Word) ∧
              (∀ j, j < k → dwordAt (headersParentHash_out thisBytes C0) j =
                dwordAt (keccakBodyDigest parentBytes N rem) j) ∧
              dwordAt (headersParentHash_out thisBytes C0) k ≠
                dwordAt (keccakBodyDigest parentBytes N rem) k⌝ **
            (hvphPost sp0 thisPtr parentPtr ret (2 : Word) vals thisBytes parentBytes **
              hvphMatchExitExtra spC parentPtr parentLen v20 vals parentBytes
                (headersParentHash_out thisBytes C0)
                (keccakBodyDigest parentBytes N rem) N rem F)) s) := by
  intro out0 Amb
  by_cases hst : headersParentHash_status thisBytes = (0 : Word)
  · by_cases heq0 : dwordAt (headersParentHash_out thisBytes C0) 0 =
      dwordAt (keccakBodyDigest parentBytes N rem) 0
    · by_cases heq1 : dwordAt (headersParentHash_out thisBytes C0) 1 =
        dwordAt (keccakBodyDigest parentBytes N rem) 1
      · by_cases heq2 : dwordAt (headersParentHash_out thisBytes C0) 2 =
          dwordAt (keccakBodyDigest parentBytes N rem) 2
        · by_cases heq3 : dwordAt (headersParentHash_out thisBytes C0) 3 =
            dwordAt (keccakBodyDigest parentBytes N rem) 3
          · have harm := hvphUnifiedMatch sp0 spC ret thisPtr thisLen parentPtr
              parentLen vals v20 thisBytes parentBytes C0 N rem os F hF hret hspC
              hst hlenW hlen3 hclaim0 hsalign hsover hsvalid hOutLen hplen hlen
              hrem_le hos halign_zk hover hNbound hrem64 hb8i hovers hoveri
              hvalids hvalidi hvalidRem hvalid135 hvalidMem heq0 heq1 heq2 heq3
            exact cpsTripleWithin_weaken (fun _ hp => hp)
              (fun s hq => Or.inl ((sepConj_pure_left s).mpr
                ⟨⟨hst, fun q hq => by interval_cases q <;> assumption⟩, hq⟩)) harm
          · have harm := hvphUnifiedMismatch3 sp0 spC ret thisPtr thisLen parentPtr
              parentLen vals v20 thisBytes parentBytes C0 N rem os F hF hret hspC
              hst hlenW hlen3 hclaim0 hsalign hsover hsvalid hOutLen hplen hlen
              hrem_le hos halign_zk hover hNbound hrem64 hb8i hovers hoveri
              hvalids hvalidi hvalidRem hvalid135 hvalidMem heq0 heq1 heq2 heq3
            exact cpsTripleWithin_weaken (fun _ hp => hp)
              (fun s hq => Or.inr (Or.inr ⟨3, ⟨by decide, (sepConj_pure_left s).mpr
                ⟨⟨hst, ⟨fun j hj => by interval_cases j <;> assumption, heq3⟩⟩, hq⟩⟩⟩))
              (cpsTripleWithin_mono_nSteps (by omega) harm)
        · have harm := hvphUnifiedMismatch2 sp0 spC ret thisPtr thisLen parentPtr
            parentLen vals v20 thisBytes parentBytes C0 N rem os F hF hret hspC
            hst hlenW hlen3 hclaim0 hsalign hsover hsvalid hOutLen hplen hlen
            hrem_le hos halign_zk hover hNbound hrem64 hb8i hovers hoveri
            hvalids hvalidi hvalidRem hvalid135 hvalidMem heq0 heq1 heq2
          exact cpsTripleWithin_weaken (fun _ hp => hp)
            (fun s hq => Or.inr (Or.inr ⟨2, ⟨by decide, (sepConj_pure_left s).mpr
              ⟨⟨hst, ⟨fun j hj => by interval_cases j <;> assumption, heq2⟩⟩, hq⟩⟩⟩))
            (cpsTripleWithin_mono_nSteps (by omega) harm)
      · have harm := hvphUnifiedMismatch1 sp0 spC ret thisPtr thisLen parentPtr
          parentLen vals v20 thisBytes parentBytes C0 N rem os F hF hret hspC
          hst hlenW hlen3 hclaim0 hsalign hsover hsvalid hOutLen hplen hlen
          hrem_le hos halign_zk hover hNbound hrem64 hb8i hovers hoveri
          hvalids hvalidi hvalidRem hvalid135 hvalidMem heq0 heq1
        exact cpsTripleWithin_weaken (fun _ hp => hp)
          (fun s hq => Or.inr (Or.inr ⟨1, ⟨by decide, (sepConj_pure_left s).mpr
            ⟨⟨hst, ⟨fun j hj => by interval_cases j; assumption, heq1⟩⟩, hq⟩⟩⟩))
          (cpsTripleWithin_mono_nSteps (by omega) harm)
    · have harm := hvphUnifiedMismatch0 sp0 spC ret thisPtr thisLen parentPtr
        parentLen vals v20 thisBytes parentBytes C0 N rem os F hF hret hspC
        hst hlenW hlen3 hclaim0 hsalign hsover hsvalid hOutLen hplen hlen
        hrem_le hos halign_zk hover hNbound hrem64 hb8i hovers hoveri
        hvalids hvalidi hvalidRem hvalid135 hvalidMem heq0
      exact cpsTripleWithin_weaken (fun _ hp => hp)
        (fun s hq => Or.inr (Or.inr ⟨0, ⟨by decide, (sepConj_pure_left s).mpr
          ⟨⟨hst, ⟨fun j hj => absurd hj (by omega), heq0⟩⟩, hq⟩⟩⟩))
        (cpsTripleWithin_mono_nSteps (by omega) harm)
  · have hdis := hvph_headersCallPremise_of_leaf sp0 spC ret thisPtr thisLen
      parentPtr parentLen vals thisBytes C0 parentBytes hspC hlenW hlen3 hclaim0
      hsalign hsover hsvalid
    have harm0 := header_validate_parent_hash_extract_fail_spec_within 312 sp0
      spC ret thisPtr thisLen parentPtr parentLen (headersParentHash_status
      thisBytes) vals thisBytes parentBytes C0 (headersParentHash_out thisBytes
      C0) hspC hret hst hdis
    have hAmb : Amb.pcFree := hvphSuccKeccakAmb_pcFree spC v20 os out0 F hF
    have harmF := cpsTripleWithin_frameR Amb hAmb harm0
    have hle : 19 + 312 ≤ 40 + 312 + nKeccak N rem := by omega
    refine cpsTripleWithin_mono_nSteps hle
      (cpsTripleWithin_weaken (fun s hp => ?_)
        (fun s hq => Or.inr (Or.inl ((sepConj_pure_left s).mpr ⟨hst, hq⟩))) harmF)
    simp only [sepConj_assoc] at hp ⊢
    xperm_hyp hp


end EvmAsm.Codegen.HeaderValidateParentHashSpec