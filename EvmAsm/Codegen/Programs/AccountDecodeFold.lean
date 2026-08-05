/-
  EvmAsm.Codegen.Programs.AccountDecodeFold

  GH #11483: the two zero-length hash **fold arms** appended to
  `accountDecode_prog` after the epilogue.

  `witness_state.py:114-119` folds a zero-length `storage_root` / `code_hash`
  field to `EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH` rather than rejecting it.  The
  guest mirrors that with a second-level dispatch: the exact-32 `BNE` targets a
  `BEQ x6, x0` arm (`AccountDecodeDispatch`'s `adRoot/adCodeZeroDispatch`) whose
  taken edge runs the block proved here — materialise the constant's address with
  `la`, copy its 32 bytes into the output slot with four `LD`/`SD` pairs, and
  `JAL` back to the field's normal continuation.

  Both arms store with `SD` where the ordinary copy loops use `SB`, so they need
  the output slot 8-byte aligned.  That is already available: `adBBField2` carries
  `hralign`/`hcalign`, and field 1's zeroing already stores with `SD .x19`.

  Neither arm advances `x20`/`x21` the way the copy loops do (they address by
  immediate instead), which is harmless — both are restored from `savedFrame` in
  the epilogue, and `adBBField3` already takes the live `x20` as a parameter
  separate from `rootOut`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeClose4

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## The fold constants' guest addresses

    Both live in the `.data` RAM window and both are 8-byte aligned, which is
    what makes the `LD` side of each pair well-formed. -/

/-- `iw_empty_trie_root` (`MptInsertWalk.lean:349`). -/
abbrev ITR : Word := (GuestAddrs.iw_empty_trie_root : Word)

/-- `aie_empty_code_hash`. -/
abbrev ECH : Word := (GuestAddrs.aie_empty_code_hash : Word)

theorem itr_align : ITR.toNat % 8 = 0 := by decide
theorem ech_align : ECH.toNat % 8 = 0 := by decide

/-- The two `.data` constants the fold arms read, as one assertion.  Threaded
    through the field-2/3 backbones into `account_decode`'s precondition: the
    routine now *reads* guest data, which it did not before #11483. -/
def adFoldConstants : Assertion :=
  bytesRegion ITR adEmptyTrieRootBytes ** bytesRegion ECH adEmptyCodeHashBytes

theorem pcFree_adFoldConstants : adFoldConstants.pcFree := by
  unfold adFoldConstants
  exact pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)

/-! ## `la` materialisation for the two constants -/

/-- `la x5, iw_empty_trie_root` at the field-2 fold arm [138]-[139]
    (`AB+552 → AB+560`). -/
private theorem adLaItrX5_552 (v : Word) :
    cpsTripleWithin 2 (AB + 552) (AB + 560) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ ITR) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 552)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.iw_empty_trie_root
        (GuestAddrs.account_decode + 552))) a = some i → fullCode a = some i :=
    fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 552) accountDecode_prog 138
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.iw_empty_trie_root
          (GuestAddrs.account_decode + 552)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 556)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.iw_empty_trie_root
        (GuestAddrs.account_decode + 552))) a = some i → fullCode a = some i :=
    fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 556) accountDecode_prog 139
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.iw_empty_trie_root
          (GuestAddrs.account_decode + 552)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 552) ITR (by decide) (by decide) hau had
  rw [show (AB + 552 : Word) + 8 = AB + 560 from by bv_omega] at h
  exact h

/-- `la x5, aie_empty_code_hash` at the field-3 fold arm [151]-[152]
    (`AB+604 → AB+612`). -/
private theorem adLaEchX5_604 (v : Word) :
    cpsTripleWithin 2 (AB + 604) (AB + 612) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ ECH) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 604)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.aie_empty_code_hash
        (GuestAddrs.account_decode + 604))) a = some i → fullCode a = some i :=
    fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 604) accountDecode_prog 151
        (.AUIPC .x5 (Codegen.laHi GuestAddrs.aie_empty_code_hash
          (GuestAddrs.account_decode + 604)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 608)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.aie_empty_code_hash
        (GuestAddrs.account_decode + 604))) a = some i → fullCode a = some i :=
    fun a i hi => ad_mono a i
      (CodeReq.ofProg_mem_at AB (AB + 608) accountDecode_prog 152
        (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.aie_empty_code_hash
          (GuestAddrs.account_decode + 604)))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 604) ECH (by decide) (by decide) hau had
  rw [show (AB + 604 : Word) + 8 = AB + 612 from by bv_omega] at h
  exact h

/-! ## The 32-byte constant stores

    Four `LD`/`SD` pairs at dword offsets 0/8/16/24.  Both sides of every pair
    are single 8-byte `memIs` cells — which is what `bytesRegion` already *is*
    (`MemRegion.lean:21-28`), so `bytesRegion32_dwords_eq` splits source and
    destination into exactly the cells the instructions touch and no alignment
    side goals arise. -/

/-- `signExtend12` of the four dword offsets, as `Word` addition. -/
private theorem adFoldOff (base : Word) :
    base + signExtend12 (0 : BitVec 12) = base ∧
    base + signExtend12 (8 : BitVec 12) = base + 8 ∧
    base + signExtend12 (16 : BitVec 12) = base + 16 ∧
    base + signExtend12 (24 : BitVec 12) = base + 24 :=
  ⟨by rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
   by rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide],
   by rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide],
   by rw [show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide]⟩

set_option maxRecDepth 8000 in
/-- **One `LD`/`SD` pair of a fold store** (`pc → pc+8`): read the constant's
    dword at `off` through `x5` and write it to the output slot through `dst`.

    Stated over abstract code-membership hypotheses and *resolved* cell addresses,
    so both arms' four pairs are eight instantiations of one lemma rather than
    eight open-coded sequences. -/
private theorem adFoldPair (dst : Reg) (srcAddr dstAddr srcCell dstCell w wOld vOld : Word)
    (off : BitVec 12) (pc : Word)
    (hsrc : srcAddr + signExtend12 off = srcCell)
    (hdst : dstAddr + signExtend12 off = dstCell)
    (hld : ∀ a i, CodeReq.singleton pc (.LD .x7 .x5 off) a = some i → fullCode a = some i)
    (hsd : ∀ a i, CodeReq.singleton (pc + 4) (.SD dst .x7 off) a = some i → fullCode a = some i) :
    cpsTripleWithin 2 pc (pc + 8) fullCode
      (((.x5 : Reg) ↦ᵣ srcAddr) ** ((.x7 : Reg) ↦ᵣ vOld) ** (dst ↦ᵣ dstAddr) **
       (srcCell ↦ₘ w) ** (dstCell ↦ₘ wOld))
      (((.x5 : Reg) ↦ᵣ srcAddr) ** ((.x7 : Reg) ↦ᵣ w) ** (dst ↦ᵣ dstAddr) **
       (srcCell ↦ₘ w) ** (dstCell ↦ₘ w)) := by
  subst hsrc; subst hdst
  have hl := cpsTripleWithin_extend_code hld
    (ld_spec_gen_within .x7 .x5 srcAddr vOld w off pc (by decide))
  have hlf := cpsTripleWithin_frameR
    ((dst ↦ᵣ dstAddr) ** ((dstAddr + signExtend12 off) ↦ₘ wOld))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hl
  have hs := cpsTripleWithin_extend_code hsd
    (sd_spec_gen_within dst .x7 dstAddr w wOld off (pc + 4))
  have hsf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ srcAddr) ** ((srcAddr + signExtend12 off) ↦ₘ w))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hs
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlf hsf
  rw [show pc + 4 + 4 = pc + 8 from by bv_omega] at hseq
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hseq

set_option maxRecDepth 8000 in
/-- **Field-2 fold store** [138]-[147] (`AB+552 → AB+592`): materialise
    `iw_empty_trie_root` and copy its 32 bytes into the storage-root slot, so the
    slot holds `EMPTY_TRIE_ROOT` exactly — the spec's value for a zero-length
    `storage_root` field (`witness_state.py:118`).  The constant's region is
    preserved, and `x20` is *not* advanced (the stores address by immediate,
    unlike the copy loop's cursor). -/
theorem adRootFoldStore (rootOut v5 v7 : Word) (oldRoot : List (BitVec 8))
    (holdRootlen : oldRoot.length = 32) :
    cpsTripleWithin 10 (AB + 552) (AB + 592) fullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x20 : Reg) ↦ᵣ rootOut) **
       bytesRegion rootOut oldRoot ** bytesRegion ITR adEmptyTrieRootBytes)
      ((((.x5 : Reg) ↦ᵣ ITR) ** ((.x20 : Reg) ↦ᵣ rootOut) **
        bytesRegion rootOut adEmptyTrieRootBytes ** bytesRegion ITR adEmptyTrieRootBytes) **
       regOwn .x7) := by
  obtain ⟨hs0, hs8, hs16, hs24⟩ := adFoldOff ITR
  obtain ⟨hd0, hd8, hd16, hd24⟩ := adFoldOff rootOut
  rw [bytesRegion32_dwords_eq ITR adEmptyTrieRootBytes adEmptyTrieRootBytes_length,
      bytesRegion32_dwords_eq rootOut oldRoot holdRootlen,
      bytesRegion32_dwords_eq rootOut adEmptyTrieRootBytes adEmptyTrieRootBytes_length]
  have p0 := adFoldPair .x20 ITR rootOut ITR rootOut
    (packBytes (adEmptyTrieRootBytes.take 8)) (packBytes (oldRoot.take 8)) v7 (0 : BitVec 12) (AB + 560) hs0 hd0
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 560)
      accountDecode_prog 140 (.LD .x7 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 560 + 4)
      accountDecode_prog 141 (.SD .x20 .x7 (0 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 560 : Word) + 8 = AB + 568 from by bv_omega] at p0
  have p1 := adFoldPair .x20 ITR rootOut (ITR + 8) (rootOut + 8)
    (packBytes ((adEmptyTrieRootBytes.drop 8).take 8)) (packBytes ((oldRoot.drop 8).take 8)) (packBytes (adEmptyTrieRootBytes.take 8)) (8 : BitVec 12) (AB + 568) hs8 hd8
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 568)
      accountDecode_prog 142 (.LD .x7 .x5 (8 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 568 + 4)
      accountDecode_prog 143 (.SD .x20 .x7 (8 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 568 : Word) + 8 = AB + 576 from by bv_omega] at p1
  have p2 := adFoldPair .x20 ITR rootOut (ITR + 16) (rootOut + 16)
    (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8)) (packBytes (((oldRoot.drop 8).drop 8).take 8)) (packBytes ((adEmptyTrieRootBytes.drop 8).take 8)) (16 : BitVec 12) (AB + 576) hs16 hd16
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 576)
      accountDecode_prog 144 (.LD .x7 .x5 (16 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 576 + 4)
      accountDecode_prog 145 (.SD .x20 .x7 (16 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 576 : Word) + 8 = AB + 584 from by bv_omega] at p2
  have p3 := adFoldPair .x20 ITR rootOut (ITR + 24) (rootOut + 24)
    (packBytes ((((adEmptyTrieRootBytes.drop 8).drop 8).drop 8).take 8)) (packBytes ((((oldRoot.drop 8).drop 8).drop 8).take 8)) (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8)) (24 : BitVec 12) (AB + 584) hs24 hd24
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 584)
      accountDecode_prog 146 (.LD .x7 .x5 (24 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 584 + 4)
      accountDecode_prog 147 (.SD .x20 .x7 (24 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 584 : Word) + 8 = AB + 592 from by bv_omega] at p3
  have f0 := cpsTripleWithin_frameR
    (((ITR + 8) ↦ₘ (packBytes ((adEmptyTrieRootBytes.drop 8).take 8))) **
     ((ITR + 16) ↦ₘ (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8))) **
     ((ITR + 24) ↦ₘ (packBytes ((((adEmptyTrieRootBytes.drop 8).drop 8).drop 8).take 8))) **
     ((rootOut + 8) ↦ₘ (packBytes ((oldRoot.drop 8).take 8))) **
     ((rootOut + 16) ↦ₘ (packBytes (((oldRoot.drop 8).drop 8).take 8))) **
     ((rootOut + 24) ↦ₘ (packBytes ((((oldRoot.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p0
  have f1 := cpsTripleWithin_frameR
    ((ITR ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((ITR + 16) ↦ₘ (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8))) **
     ((ITR + 24) ↦ₘ (packBytes ((((adEmptyTrieRootBytes.drop 8).drop 8).drop 8).take 8))) **
     (rootOut ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((rootOut + 16) ↦ₘ (packBytes (((oldRoot.drop 8).drop 8).take 8))) **
     ((rootOut + 24) ↦ₘ (packBytes ((((oldRoot.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p1
  have f2 := cpsTripleWithin_frameR
    ((ITR ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((ITR + 8) ↦ₘ (packBytes ((adEmptyTrieRootBytes.drop 8).take 8))) **
     ((ITR + 24) ↦ₘ (packBytes ((((adEmptyTrieRootBytes.drop 8).drop 8).drop 8).take 8))) **
     (rootOut ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((rootOut + 8) ↦ₘ (packBytes ((adEmptyTrieRootBytes.drop 8).take 8))) **
     ((rootOut + 24) ↦ₘ (packBytes ((((oldRoot.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p2
  have f3 := cpsTripleWithin_frameR
    ((ITR ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((ITR + 8) ↦ₘ (packBytes ((adEmptyTrieRootBytes.drop 8).take 8))) **
     ((ITR + 16) ↦ₘ (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8))) **
     (rootOut ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((rootOut + 8) ↦ₘ (packBytes ((adEmptyTrieRootBytes.drop 8).take 8))) **
     ((rootOut + 16) ↦ₘ (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p3
  have hla := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7) **
     ((.x20 : Reg) ↦ᵣ rootOut) **
     (ITR ↦ₘ (packBytes (adEmptyTrieRootBytes.take 8))) **
     ((ITR + 8) ↦ₘ (packBytes ((adEmptyTrieRootBytes.drop 8).take 8))) **
     ((ITR + 16) ↦ₘ (packBytes (((adEmptyTrieRootBytes.drop 8).drop 8).take 8))) **
     ((ITR + 24) ↦ₘ (packBytes ((((adEmptyTrieRootBytes.drop 8).drop 8).drop 8).take 8))) **
     (rootOut ↦ₘ (packBytes (oldRoot.take 8))) **
     ((rootOut + 8) ↦ₘ (packBytes ((oldRoot.drop 8).take 8))) **
     ((rootOut + 16) ↦ₘ (packBytes (((oldRoot.drop 8).drop 8).take 8))) **
     ((rootOut + 24) ↦ₘ (packBytes ((((oldRoot.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (adLaItrX5_552 v5)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla f0
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f1
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f2
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => sepConj_mono_right (regIs_implies_regOwn .x7) h (by xperm_hyp hq)) s4)

#print axioms adRootFoldStore

set_option maxRecDepth 8000 in
/-- **Field-3 fold store** [151]-[160] (`AB+604 → AB+644`): the same shape for
    `aie_empty_code_hash` into the code-hash slot — `EMPTY_CODE_HASH` for a
    zero-length `code_hash` field (`witness_state.py:119`). -/
theorem adCodeFoldStore (codeOut v5 v7 : Word) (oldCode : List (BitVec 8))
    (holdCodelen : oldCode.length = 32) :
    cpsTripleWithin 10 (AB + 604) (AB + 644) fullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x7 : Reg) ↦ᵣ v7) ** ((.x21 : Reg) ↦ᵣ codeOut) **
       bytesRegion codeOut oldCode ** bytesRegion ECH adEmptyCodeHashBytes)
      ((((.x5 : Reg) ↦ᵣ ECH) ** ((.x21 : Reg) ↦ᵣ codeOut) **
        bytesRegion codeOut adEmptyCodeHashBytes ** bytesRegion ECH adEmptyCodeHashBytes) **
       regOwn .x7) := by
  obtain ⟨hs0, hs8, hs16, hs24⟩ := adFoldOff ECH
  obtain ⟨hd0, hd8, hd16, hd24⟩ := adFoldOff codeOut
  rw [bytesRegion32_dwords_eq ECH adEmptyCodeHashBytes adEmptyCodeHashBytes_length,
      bytesRegion32_dwords_eq codeOut oldCode holdCodelen,
      bytesRegion32_dwords_eq codeOut adEmptyCodeHashBytes adEmptyCodeHashBytes_length]
  have p0 := adFoldPair .x21 ECH codeOut ECH codeOut
    (packBytes (adEmptyCodeHashBytes.take 8)) (packBytes (oldCode.take 8)) v7 (0 : BitVec 12) (AB + 612) hs0 hd0
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 612)
      accountDecode_prog 153 (.LD .x7 .x5 (0 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 612 + 4)
      accountDecode_prog 154 (.SD .x21 .x7 (0 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 612 : Word) + 8 = AB + 620 from by bv_omega] at p0
  have p1 := adFoldPair .x21 ECH codeOut (ECH + 8) (codeOut + 8)
    (packBytes ((adEmptyCodeHashBytes.drop 8).take 8)) (packBytes ((oldCode.drop 8).take 8)) (packBytes (adEmptyCodeHashBytes.take 8)) (8 : BitVec 12) (AB + 620) hs8 hd8
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 620)
      accountDecode_prog 155 (.LD .x7 .x5 (8 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 620 + 4)
      accountDecode_prog 156 (.SD .x21 .x7 (8 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 620 : Word) + 8 = AB + 628 from by bv_omega] at p1
  have p2 := adFoldPair .x21 ECH codeOut (ECH + 16) (codeOut + 16)
    (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8)) (packBytes (((oldCode.drop 8).drop 8).take 8)) (packBytes ((adEmptyCodeHashBytes.drop 8).take 8)) (16 : BitVec 12) (AB + 628) hs16 hd16
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 628)
      accountDecode_prog 157 (.LD .x7 .x5 (16 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 628 + 4)
      accountDecode_prog 158 (.SD .x21 .x7 (16 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 628 : Word) + 8 = AB + 636 from by bv_omega] at p2
  have p3 := adFoldPair .x21 ECH codeOut (ECH + 24) (codeOut + 24)
    (packBytes ((((adEmptyCodeHashBytes.drop 8).drop 8).drop 8).take 8)) (packBytes ((((oldCode.drop 8).drop 8).drop 8).take 8)) (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8)) (24 : BitVec 12) (AB + 636) hs24 hd24
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 636)
      accountDecode_prog 159 (.LD .x7 .x5 (24 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
    (fun a i hi => ad_mono a i (CodeReq.ofProg_mem_at AB (AB + 636 + 4)
      accountDecode_prog 160 (.SD .x21 .x7 (24 : BitVec 12)) (by bv_omega)
      (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi))
  rw [show (AB + 636 : Word) + 8 = AB + 644 from by bv_omega] at p3
  have f0 := cpsTripleWithin_frameR
    (((ECH + 8) ↦ₘ (packBytes ((adEmptyCodeHashBytes.drop 8).take 8))) **
     ((ECH + 16) ↦ₘ (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8))) **
     ((ECH + 24) ↦ₘ (packBytes ((((adEmptyCodeHashBytes.drop 8).drop 8).drop 8).take 8))) **
     ((codeOut + 8) ↦ₘ (packBytes ((oldCode.drop 8).take 8))) **
     ((codeOut + 16) ↦ₘ (packBytes (((oldCode.drop 8).drop 8).take 8))) **
     ((codeOut + 24) ↦ₘ (packBytes ((((oldCode.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p0
  have f1 := cpsTripleWithin_frameR
    ((ECH ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((ECH + 16) ↦ₘ (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8))) **
     ((ECH + 24) ↦ₘ (packBytes ((((adEmptyCodeHashBytes.drop 8).drop 8).drop 8).take 8))) **
     (codeOut ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((codeOut + 16) ↦ₘ (packBytes (((oldCode.drop 8).drop 8).take 8))) **
     ((codeOut + 24) ↦ₘ (packBytes ((((oldCode.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p1
  have f2 := cpsTripleWithin_frameR
    ((ECH ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((ECH + 8) ↦ₘ (packBytes ((adEmptyCodeHashBytes.drop 8).take 8))) **
     ((ECH + 24) ↦ₘ (packBytes ((((adEmptyCodeHashBytes.drop 8).drop 8).drop 8).take 8))) **
     (codeOut ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((codeOut + 8) ↦ₘ (packBytes ((adEmptyCodeHashBytes.drop 8).take 8))) **
     ((codeOut + 24) ↦ₘ (packBytes ((((oldCode.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p2
  have f3 := cpsTripleWithin_frameR
    ((ECH ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((ECH + 8) ↦ₘ (packBytes ((adEmptyCodeHashBytes.drop 8).take 8))) **
     ((ECH + 16) ↦ₘ (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8))) **
     (codeOut ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((codeOut + 8) ↦ₘ (packBytes ((adEmptyCodeHashBytes.drop 8).take 8))) **
     ((codeOut + 16) ↦ₘ (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_memIs | apply pcFree_sepConj) p3
  have hla := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7) **
     ((.x21 : Reg) ↦ᵣ codeOut) **
     (ECH ↦ₘ (packBytes (adEmptyCodeHashBytes.take 8))) **
     ((ECH + 8) ↦ₘ (packBytes ((adEmptyCodeHashBytes.drop 8).take 8))) **
     ((ECH + 16) ↦ₘ (packBytes (((adEmptyCodeHashBytes.drop 8).drop 8).take 8))) **
     ((ECH + 24) ↦ₘ (packBytes ((((adEmptyCodeHashBytes.drop 8).drop 8).drop 8).take 8))) **
     (codeOut ↦ₘ (packBytes (oldCode.take 8))) **
     ((codeOut + 8) ↦ₘ (packBytes ((oldCode.drop 8).take 8))) **
     ((codeOut + 16) ↦ₘ (packBytes (((oldCode.drop 8).drop 8).take 8))) **
     ((codeOut + 24) ↦ₘ (packBytes ((((oldCode.drop 8).drop 8).drop 8).take 8))))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj)
    (adLaEchX5_604 v5)
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla f0
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 f1
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 f2
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 f3
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => sepConj_mono_right (regIs_implies_regOwn .x7) h (by xperm_hyp hq)) s4)

#print axioms adCodeFoldStore

/-! ## The rejoin jumps

    Each arm's last instruction returns control to the *same* point the ordinary
    copy path reaches, which is what makes the fold transparent to everything
    downstream: field 2 rejoins the field-3 call setup, field 3 rejoins the
    success-status store. -/

set_option maxRecDepth 8000 in
/-- Field-2 fold rejoin [148] (`AB+592 → AB+392`): `jal x0, -200` back to the
    post-field-2 continuation — exactly where the 32-byte copy loop's exit lands,
    so `adBBField3` serves both arms. -/
theorem adRootFoldJal :
    cpsTripleWithin 1 (AB + 592) (AB + 392) fullCode empAssertion empAssertion := by
  have hjal := jal_x0_spec_gen_within (-200 : BitVec 21) (AB + 592)
  rw [show (AB + 592 : Word) + signExtend21 (-200 : BitVec 21) = AB + 392 from by
    rw [show signExtend21 (-200 : BitVec 21) = (-200 : Word) from by decide]; bv_omega] at hjal
  exact cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 592) accountDecode_prog 148
        (.JAL .x0 (-200 : BitVec 21)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hjal)

#print axioms adRootFoldJal

set_option maxRecDepth 8000 in
/-- Field-3 fold rejoin [161] (`AB+644 → AB+496`): `jal x0, -148` to the
    success-status store `LI x10, 0`, where field 3's copy loop also lands. -/
theorem adCodeFoldJal :
    cpsTripleWithin 1 (AB + 644) (AB + 496) fullCode empAssertion empAssertion := by
  have hjal := jal_x0_spec_gen_within (-148 : BitVec 21) (AB + 644)
  rw [show (AB + 644 : Word) + signExtend21 (-148 : BitVec 21) = AB + 496 from by
    rw [show signExtend21 (-148 : BitVec 21) = (-148 : Word) from by decide]; bv_omega] at hjal
  exact cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 644) accountDecode_prog 161
        (.JAL .x0 (-148 : BitVec 21)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hjal)

#print axioms adCodeFoldJal

end EvmAsm.Codegen.AccountDecodeSpec
