/-
  K146 chain-encoding call composition.

  The preceding module proves the linked chain-id byte loop.  This module
  materializes the two linked chain-buffer pointers, the fixed source length,
  and the H+224 `rlp_encode_uint_be` call.  The call adapter remains the
  existing deployed triple from `TxSigningHashLegacySpecCore`; this file only
  supplies the caller-side composition and the ownership-to-value bridge for
  x28, which the loop deliberately leaves owned.
-/

import EvmAsm.Codegen.Programs.TxSigningHashLegacyChainCompose

namespace EvmAsm.Codegen.TxSigningHashLegacyUintCompose

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashLegacySpec
open EvmAsm.Codegen.TxSigningHashLegacyCompose
open EvmAsm.Codegen.TxSigningHashLegacyLoopSpec
open EvmAsm.Codegen.TxSigningHashLegacyChainCompose

/-! ## Linked argument setup at H+204 -/

theorem legacyChainPtr_spec (v10 : Word) :
    cpsTripleWithin 2 (legacyH + 204) (legacyH + 212) legacyFullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ legacyLinkedChainPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 204)
        (.AUIPC .x10 (Rv64.laHi (legacyH + 204) legacyLinkedChainPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 204) 51
      (.AUIPC .x10 (Codegen.laHi GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 204))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_chain_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 204) + 4)
        (.ADDI .x10 .x10 (Rv64.laLo (legacyH + 204) legacyLinkedChainPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 208) 52
      (.ADDI .x10 .x10 (Codegen.laLo GuestAddrs.t155_chain_be
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 204))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 204 : Word) + 4 = legacyH + 208 := by decide
    rw [hpc, ← legacy_la_chain_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x10 v10 (legacyH + 204)
    legacyLinkedChainPtr (by decide) legacy_la_chain_range hau had
  rw [show (legacyH + 204 : Word) + 8 = legacyH + 212 from by decide] at hla
  exact hla

theorem legacyChainLen_spec (v11 : Word) :
    cpsTripleWithin 1 (legacyH + 212) (legacyH + 216) legacyFullCode
      (.x11 ↦ᵣ v11) (.x11 ↦ᵣ (8 : Word)) := by
  have hli := li_spec_gen_within .x11 v11 (8 : Word)
    (legacyH + 212) (by decide)
  rw [show (legacyH + 212 : Word) + 4 = legacyH + 216 from by decide] at hli
  exact cpsTripleWithin_extend_code
    (legacy_mem_at (legacyH + 212) 53 (.LI .x11 (8 : Word))
      (by decide) (by decide) (by intro h; rfl)) hli

theorem legacyChainEncPtr_spec (v12 : Word) :
    cpsTripleWithin 2 (legacyH + 216) (legacyH + 224) legacyFullCode
      (.x12 ↦ᵣ v12) (.x12 ↦ᵣ legacyLinkedChainEncPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (legacyH + 216)
        (.AUIPC .x12 (Rv64.laHi (legacyH + 216) legacyLinkedChainEncPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 216) 54
      (.AUIPC .x12 (Codegen.laHi GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 216))) (by decide)
      (by decide) (by intro h; rfl)
    exact hmem a i (by rwa [← legacy_la_chain_enc_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((legacyH + 216) + 4)
        (.ADDI .x12 .x12 (Rv64.laLo (legacyH + 216) legacyLinkedChainEncPtr)) a =
          some i → legacyFullCode a = some i := by
    intro a i hi
    have hmem := legacy_mem_at (legacyH + 220) 55
      (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.t155_chain_enc
        (GuestAddrs.tx_signing_hash_legacy_eip155 + 216))) (by decide)
      (by decide) (by intro h; rfl)
    have hpc : (legacyH + 216 : Word) + 4 = legacyH + 220 := by decide
    rw [hpc, ← legacy_la_chain_enc_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x12 v12 (legacyH + 216)
    legacyLinkedChainEncPtr (by decide) legacy_la_chain_enc_range hau had
  rw [show (legacyH + 216 : Word) + 8 = legacyH + 224 from by decide] at hla
  exact hla

/-! The five instructions above the Uint call, framed over the loop result. -/

theorem legacyChainArgSetup_spec
    (v1 v10 v11 v12 chainId : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin 8 (legacyH + 204) (legacyH + 224) legacyFullCode
      (((.x1 : Reg) ↦ᵣ v1) ** ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr +
        BitVec.ofNat 64 8)) ** ((.x6 : Reg) ↦ᵣ (-1 : Word)) **
        regOwn .x7 ** ((.x10 : Reg) ↦ᵣ v10) **
        ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) **
        ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
        ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F) := by
  have h10 := legacyChainPtr_spec v10
  have h10F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) **
      ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
      ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
      ((.x11 : Reg) ↦ᵣ v11) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
    (by pcf; exact hF) h10
  have h10W : cpsTripleWithin 2 (legacyH + 204) (legacyH + 212)
      legacyFullCode
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ v10) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x18 : Reg) ↦ᵣ chainId) **
        regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x18 : Reg) ↦ᵣ chainId) **
        regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h10F
  have h11 := legacyChainLen_spec v11
  have h11F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) **
      ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
      ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
      ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
      ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
    (by pcf; exact hF) h11
  have h11W : cpsTripleWithin 1 (legacyH + 212) (legacyH + 216)
      legacyFullCode
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x11 : Reg) ↦ᵣ v11) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x18 : Reg) ↦ᵣ chainId) **
        regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x18 : Reg) ↦ᵣ chainId) **
        regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h11F
  have h12 := legacyChainEncPtr_spec v12
  have h12F := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ v1) **
      ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
      ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
      ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
      ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
    (by pcf; exact hF) h12
  have h12W : cpsTripleWithin 2 (legacyH + 216) (legacyH + 224)
      legacyFullCode
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ v12) ** ((.x18 : Reg) ↦ᵣ chainId) **
        regOwn .x28 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F)
      (((.x1 : Reg) ↦ᵣ v1) **
        ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
        ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
        ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) ** ((.x11 : Reg) ↦ᵣ (8 : Word)) **
        ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
        ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion legacyLinkedChainPtr (chainBytes chainId) ** F) := by
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h12F
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h10W h11W
  have hfinal := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) h01 h12W
  exact cpsTripleWithin_mono_nSteps (nSteps' := 8) (by omega) hfinal

/-! ## The linked `rlp_encode_uint_be` call at H+224 -/

def legacyChainEncOld : List (BitVec 8) := List.replicate 9 (0 : BitVec 8)

def legacyChainUintPre
    (v1 v29 v30 v31 chainId : Word) (F : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ v1) **
  ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
  ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
  ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) **
  ((.x11 : Reg) ↦ᵣ (BitVec.ofNat 64 8)) **
  ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
  ((.x18 : Reg) ↦ᵣ chainId) ** regOwn .x28 **
  ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
  ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
  bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F

def legacyChainUintPost
    (chainId : Word) (F : Assertion) : Assertion :=
  ((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
  ((.x10 : Reg) ↦ᵣ BitVec.ofNat 64
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length) **
  ((.x11 : Reg) ↦ᵣ (BitVec.ofNat 64 8)) ** regOwn .x5 ** regOwn .x6 **
  regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
  ((.x18 : Reg) ↦ᵣ chainId) ** ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
  bytesRegion legacyLinkedChainEncPtr
    (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId) ++
      legacyChainEncOld.drop
        (RlpEncodeUintBeSAsm.reubOut (chainBytes chainId)).length) ** F

/-- The K146 chain-buffer state reaches the deployed Uint call with `x28`
    owned.  The ownership conversion is explicit: the proof below first
    proves the call for every concrete `x28` value and then peels that value
    into `regOwn .x28`; no caller-side value is assumed for an owned register. -/
theorem legacyChainUintCall_spec
    (v1 v29 v30 v31 chainId : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTripleWithin
      (1 + (8 * 6 + 7 *
        (8 - RlpEncodeUintBeSAsm.reubZeros (chainBytes chainId) 0 8) + 17))
      legacyUintJalPC (legacyUintJalPC + 4) legacyFullCode
      (legacyChainUintPre v1 v29 v30 v31 chainId F)
      (legacyChainUintPost chainId F) := by
  let Pbase : Assertion :=
    ((.x1 : Reg) ↦ᵣ v1) **
    ((.x5 : Reg) ↦ᵣ (legacyLinkedChainPtr + BitVec.ofNat 64 8)) **
    ((.x6 : Reg) ↦ᵣ (-1 : Word)) ** regOwn .x7 **
    ((.x10 : Reg) ↦ᵣ legacyLinkedChainPtr) **
    ((.x11 : Reg) ↦ᵣ (BitVec.ofNat 64 8)) **
    ((.x12 : Reg) ↦ᵣ legacyLinkedChainEncPtr) **
    ((.x18 : Reg) ↦ᵣ chainId) **
    ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
    ((.x31 : Reg) ↦ᵣ v31) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    bytesRegion legacyLinkedChainPtr (chainBytes chainId) **
    bytesRegion legacyLinkedChainEncPtr legacyChainEncOld ** F
  have hfor : ∀ v28, cpsTripleWithin
      (1 + (8 * 6 + 7 *
        (8 - RlpEncodeUintBeSAsm.reubZeros (chainBytes chainId) 0 8) + 17))
      legacyUintJalPC (legacyUintJalPC + 4) legacyFullCode
      (Pbase ** ((.x28 : Reg) ↦ᵣ v28))
      (legacyChainUintPost chainId F) := by
    intro v28
    let Fcall : Assertion :=
      regOwn .x7 ** ((.x18 : Reg) ↦ᵣ chainId) ** F
    have hFcall : Fcall.pcFree := by
      dsimp [Fcall]
      pcf
      exact hF
    have hcall := legacyUint_callWithin
      v1 legacyLinkedChainPtr legacyLinkedChainEncPtr
      (chainBytes chainId) legacyChainEncOld
      (legacyLinkedChainPtr + BitVec.ofNat 64 8) (-1 : Word) v28
      v29 v30 v31 Fcall hFcall
      (by rw [chainBytes_length]) (by simp [legacyChainEncOld])
      (by decide) (by decide) (by decide) (by decide)
      (by intro k hk; interval_cases k <;> decide)
      (by intro k hk; interval_cases k <;> decide)
    exact cpsTripleWithin_weaken
      (P := ((.x1 : Reg) ↦ᵣ v1) **
        (legacyUintPre legacyLinkedChainPtr legacyLinkedChainEncPtr
          (chainBytes chainId) legacyChainEncOld
          (legacyLinkedChainPtr + BitVec.ofNat 64 8) (-1 : Word)
          v28 v29 v30 v31 ** Fcall))
      (P' := Pbase ** ((.x28 : Reg) ↦ᵣ v28))
      (Q := ((.x1 : Reg) ↦ᵣ (legacyUintJalPC + 4)) **
        (legacyUintPost legacyLinkedChainPtr legacyLinkedChainEncPtr
          (chainBytes chainId) legacyChainEncOld ** Fcall))
      (Q' := legacyChainUintPost chainId F)
      (fun _ hp => by
        dsimp [Pbase, Fcall, legacyUintPre] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        dsimp [Fcall, legacyUintPost, legacyChainUintPost] at hq ⊢
        xperm_hyp hq) hcall
  have hown := cpsTripleWithin_of_forall_regIs_to_regOwn
    (r := .x28) hfor
  exact cpsTripleWithin_weaken
    (P := Pbase ** regOwn .x28)
    (P' := legacyChainUintPre v1 v29 v30 v31 chainId F)
    (Q := legacyChainUintPost chainId F)
    (Q' := legacyChainUintPost chainId F)
    (fun _ hp => by
      dsimp [Pbase, legacyChainUintPre] at hp ⊢
      xperm_hyp hp)
    (fun _ hq => hq) hown

end EvmAsm.Codegen.TxSigningHashLegacyUintCompose
