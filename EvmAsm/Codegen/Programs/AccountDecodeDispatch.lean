/-
  The per-field length-check dispatches of `accountDecode_prog`
  (`Programs/State.lean`, PR-K27).  After each field's K20 call succeeds, the
  selected content length (`ad_length` cell) is loaded and compared:

    * field 0 (nonce)   [23]-[27] (`AB+92 → 504/112`):  `bltu 8, len`  → fail if `8 < len`.
    * field 1 (balance) [50]-[54] (`AB+200 → 504/220`): `bltu 32, len` → fail if `32 < len`.
    * field 2 (root)    [81]-[85] (`AB+324 → 504/344`): `bne  len, 32` → fail if `len ≠ 32`.
    * field 3 (code)    [107]-[111] (`AB+428 → 504/448`): `bne len, 32` → fail if `len ≠ 32`.

  Each dispatch is `la x5, ad_length ;; ld x6 ;; li x7,imm ;; branch`, a
  five-step `cpsBranchWithin` with the shared failure edge `AB+504` (the
  `li a0,1` fail tail) and a per-field continue edge.  Mirrors
  `WithdrawalDecodeSpec.wdLenCheck`.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeCall
import EvmAsm.Codegen.Programs.AccountDecodeStrip
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm (Saved savedVals listNthFrame flatReturnResult
  Success Result)

local macro "pcFreeR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-! ## K20 post-call status dispatch (all four fields)

    After a field's K20 call returns `flatReturnResult`, `BNE x10, x0` routes a
    nonzero status to the shared failure tail (`AB+504`, the `li a0,1`) and a
    zero status (a genuine `Success`) to the next phase (`dispatchPC + 4`).
    All four fields share this shape (only the guest PC / branch offset differ),
    so one theorem — parameterised on the dispatch PC, branch offset, index, and
    the concrete `BNE` fetch fact — covers every field.  Mirrors `k20Dispatch`. -/

/-- Continue-exit post (status `0`, a genuine K20 `Success`) of a field's
    post-call dispatch. -/
def adK20ContPost (spW listBase : Word) (index : Nat)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ offset len v11 v12,
    ((⌜Success bytes listBase listLen index offset len⌝ : Assertion) **
     ((((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
       ((.x10 ↦ᵣ (0 : Word)) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len))))) h

/-- Fail-exit post (nonzero status) of a field's post-call dispatch. -/
def adK20FailPost (spW listBase oldOffset oldLen : Word) (index : Nat)
    (saved : Saved) (bytes : List (BitVec 8)) (listLen : Nat) : Assertion :=
  fun h => ∃ status offset len v11 v12,
    ((⌜Result bytes listBase listLen index oldOffset oldLen status offset len ∧
        status ≠ (0 : Word)⌝ : Assertion) **
     ((((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
       ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
        regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
        (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len))))) h

set_option maxRecDepth 8000 in
/-- Generic K20 post-call status dispatch: `BNE x10, x0 bneOff` at `dispatchPC`
    routes nonzero status → `AB+504` (fail) and status `0` → `dispatchPC+4`
    (continue).  The concrete branch fetch and its taken target are supplied by
    the caller (one per field). -/
theorem adK20Dispatch (spW listBase oldOffset oldLen dispatchPC : Word)
    (bneOff : BitVec 13) (index : Nat) (saved : Saved)
    (bytes : List (BitVec 8)) (listLen : Nat)
    (htaken : dispatchPC + signExtend13 bneOff = AB + 552)
    (hmem : ∀ a i, CodeReq.singleton dispatchPC (.BNE .x10 .x0 bneOff) a = some i →
      fullCode a = some i) :
    cpsBranchWithin 1 dispatchPC fullCode
      (flatReturnResult spW listBase (BitVec.ofNat 64 index) adOffsetAddr adLengthAddr
        oldOffset oldLen saved bytes listLen index)
      (AB + 552) (adK20FailPost spW listBase oldOffset oldLen index saved bytes listLen)
      (dispatchPC + 4) (adK20ContPost spW listBase index saved bytes listLen) := by
  refine cpsBranchWithin_weaken (P := fun h => ∃ status offset len v11 v12,
      ((((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
        ((.x10 ↦ᵣ status) ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
         regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion listBase bytes **
         (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len))) **
       ⌜Result bytes listBase listLen index oldOffset oldLen status offset len⌝) h)
    (fun h hp => hp) (fun _ hq => hq) (fun _ hq => hq) ?_
  refine cpsBranchWithin_exists_pre (fun status => ?_)
  refine cpsBranchWithin_exists_pre (fun offset => ?_)
  refine cpsBranchWithin_exists_pre (fun len => ?_)
  refine cpsBranchWithin_exists_pre (fun v11 => ?_)
  refine cpsBranchWithin_exists_pre (fun v12 => ?_)
  let REST : Assertion :=
    (((.x2 ↦ᵣ spW) ** regsAt listNthFrame (savedVals saved) ** stackFree spW 8) **
     (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwn .x13 ** regOwn .x14 **
      regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
      bytesRegion listBase bytes **
      (adOffsetAddr ↦ₘ offset) ** (adLengthAddr ↦ₘ len))) **
    ⌜Result bytes listBase listLen index oldOffset oldLen status offset len⌝
  have hbne := bne_spec_gen_within .x10 .x0 bneOff status (0 : Word) dispatchPC
  rw [htaken, show (dispatchPC : Word) + 4 = dispatchPC + 4 from rfl] at hbne
  have hbneL := cpsBranchWithin_extend_code hmem hbne
  have hbneF := cpsBranchWithin_frameR REST (by unfold REST; pcf) hbneL
  refine cpsBranchWithin_weaken (fun h hp => by
      unfold REST
      xperm_hyp hp)
    (fun h hq => by
      refine ⟨status, offset, len, v11, v12, ?_⟩
      unfold REST at hq
      obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
      have hne : status ≠ (0 : Word) := ((sepConj_pure_right h4).1 hrest).2
      have hx0 : ((.x0 : Reg) ↦ᵣ (0 : Word)) h4 := ((sepConj_pure_right h4).1 hrest).1
      have hbody := ((sepConj_pure_right h2).1 hR).1
      have hres := ((sepConj_pure_right h2).1 hR).2
      apply (sepConj_pure_left h).2
      refine ⟨⟨hres, hne⟩, ?_⟩
      have hq' : (((.x10 ↦ᵣ status) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** _) h :=
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hx10, hx0⟩, hbody⟩
      xperm_hyp hq')
    (fun h hq => by
      unfold REST at hq
      obtain ⟨h1, h2, hd, hu, hA, hR⟩ := hq
      obtain ⟨h3, h4, hd2, hu2, hx10, hrest⟩ := hA
      have hz : status = (0 : Word) := ((sepConj_pure_right h4).1 hrest).2
      have hx0 : ((.x0 : Reg) ↦ᵣ (0 : Word)) h4 := ((sepConj_pure_right h4).1 hrest).1
      have hres := ((sepConj_pure_right h2).1 hR).2
      have hbody := ((sepConj_pure_right h2).1 hR).1
      have hsucc : Success bytes listBase listLen index offset len := by
        rw [hz] at hres
        cases hres with
        | ok o l hok => exact hok
      refine ⟨offset, len, v11, v12, ?_⟩
      subst hz
      apply (sepConj_pure_left h).2
      refine ⟨hsucc, ?_⟩
      have hq' : (((.x10 ↦ᵣ (0 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word))) ** _) h :=
        ⟨h1, h2, hd, hu, ⟨h3, h4, hd2, hu2, hx10, hx0⟩, hbody⟩
      xperm_hyp hq')
    hbneF

#print axioms adK20Dispatch

/-! ## `la x5, ad_length` materialisers for the four length-check sites -/

/-- `la x5, ad_length` at field 0 [23]-[24] (`AB+92 → AB+100`). -/
private theorem adLaLenX5_92 (v : Word) :
    cpsTripleWithin 2 (AB + 92) (AB + 100) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 92)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 92) accountDecode_prog 23
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 96)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 96) accountDecode_prog 24
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 92)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 92) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 92 : Word) + 8 = AB + 100 from by bv_omega] at h
  exact h

/-- `la x5, ad_length` at field 1 [50]-[51] (`AB+200 → AB+208`). -/
private theorem adLaLenX5_200 (v : Word) :
    cpsTripleWithin 2 (AB + 224) (AB + 232) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 224)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 224)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 224) accountDecode_prog 56
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 224)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 228)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 224)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 228) accountDecode_prog 57
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 224)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 224) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 224 : Word) + 8 = AB + 232 from by bv_omega] at h
  exact h

/-- `la x5, ad_length` at field 2 [81]-[82] (`AB+324 → AB+332`). -/
private theorem adLaLenX5_324 (v : Word) :
    cpsTripleWithin 2 (AB + 372) (AB + 380) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 372)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 372)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 372) accountDecode_prog 93
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 372)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 376)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 372)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 376) accountDecode_prog 94
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 372)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 372) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 372 : Word) + 8 = AB + 380 from by bv_omega] at h
  exact h

/-- `la x5, ad_length` at field 3 [107]-[108] (`AB+428 → AB+436`). -/
private theorem adLaLenX5_428 (v : Word) :
    cpsTripleWithin 2 (AB + 476) (AB + 484) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adLengthAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 476)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 476)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 476) accountDecode_prog 119
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_length (GuestAddrs.account_decode + 476)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 480)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 476)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 480) accountDecode_prog 120
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_length (GuestAddrs.account_decode + 476)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 476) adLengthAddr (by decide) (by decide) hau had
  rw [show (AB + 476 : Word) + 8 = AB + 484 from by bv_omega] at h
  exact h

/-- `la x5, ad_offset` at field-0 value-check [26]-[27] (`AB+104 → AB+112`). -/
private theorem adLaOffX5_104 (v : Word) :
    cpsTripleWithin 2 (AB + 104) (AB + 112) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 104)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 104)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 104) accountDecode_prog 26
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 104)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 108)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 104)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 108) accountDecode_prog 27
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 104)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 104) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 104 : Word) + 8 = AB + 112 from by bv_omega] at h
  exact h

/-- `la x5, ad_offset` at field-1 value-check [59]-[60] (`AB+236 → AB+244`). -/
private theorem adLaOffX5_236 (v : Word) :
    cpsTripleWithin 2 (AB + 236) (AB + 244) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 236)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 236)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 236) accountDecode_prog 59
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 236)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 240)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 236)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 240) accountDecode_prog 60
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 236)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 236) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 236 : Word) + 8 = AB + 244 from by bv_omega] at h
  exact h

private theorem ad_len_eq_ofNat (len : Word) :
    BitVec.ofNat 64 len.toNat = len := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt len.isLt]

private theorem ad_off_eq_ofNat (offset : Word) :
    BitVec.ofNat 64 offset.toNat = offset := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offset.isLt]

private theorem ad_add_base_off (listBase offset : Word) :
    listBase + offset = listBase + BitVec.ofNat 64 offset.toNat := by
  rw [ad_off_eq_ofNat]

private theorem ad_sigLen_toNat (bytes : List (BitVec 8)) (o0 n : Nat)
    (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 (n - nlzWin bytes o0 n))).toNat = n - nlzWin bytes o0 n := by
  have hnz := nlzWin_le bytes o0 n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

private theorem ad_sigLen_ult8 (bytes : List (BitVec 8)) (o0 n : Nat)
    (hn : n < 2 ^ 64) :
    BitVec.ult (8 : Word) (BitVec.ofNat 64 (n - nlzWin bytes o0 n)) = true ↔
      8 < n - nlzWin bytes o0 n := by
  have hs := ad_sigLen_toNat bytes o0 n hn
  have h8 : ((8 : Word)).toNat = 8 := by decide
  simp only [BitVec.ult, decide_eq_true_eq, hs, h8]

private theorem ad_sigLen_ult32 (bytes : List (BitVec 8)) (o0 n : Nat)
    (hn : n < 2 ^ 64) :
    BitVec.ult (32 : Word) (BitVec.ofNat 64 (n - nlzWin bytes o0 n)) = true ↔
      32 < n - nlzWin bytes o0 n := by
  have hs := ad_sigLen_toNat bytes o0 n hn
  have h32 : ((32 : Word)).toNat = 32 := by decide
  simp only [BitVec.ult, decide_eq_true_eq, hs, h32]

theorem ad_nonceValueOk_iff (bytes : List (BitVec 8)) (offset len : Word)
    (hbound : offset.toNat + len.toNat ≤ bytes.length) :
    nonceValueOk bytes offset len ↔
      len.toNat - nlzWin bytes offset.toNat len.toNat ≤ 8 := by
  unfold nonceValueOk fieldContent
  rw [significantLen_eq_nlzWin bytes offset.toNat len.toNat hbound]

theorem ad_balanceValueOk_iff (bytes : List (BitVec 8)) (offset len : Word)
    (hbound : offset.toNat + len.toNat ≤ bytes.length) :
    balanceValueOk bytes offset len ↔
      len.toNat - nlzWin bytes offset.toNat len.toNat ≤ 32 := by
  unfold balanceValueOk fieldContent
  rw [significantLen_eq_nlzWin bytes offset.toNat len.toNat hbound]

theorem ad_sigLen_ult8_public (bytes : List (BitVec 8)) (o0 n : Nat)
    (hn : n < 2 ^ 64) :
    BitVec.ult (8 : Word) (BitVec.ofNat 64 (n - nlzWin bytes o0 n)) = true ↔
      8 < n - nlzWin bytes o0 n :=
  ad_sigLen_ult8 bytes o0 n hn

theorem ad_sigLen_ult32_public (bytes : List (BitVec 8)) (o0 n : Nat)
    (hn : n < 2 ^ 64) :
    BitVec.ult (32 : Word) (BitVec.ofNat 64 (n - nlzWin bytes o0 n)) = true ↔
      32 < n - nlzWin bytes o0 n :=
  ad_sigLen_ult32 bytes o0 n hn

set_option maxRecDepth 8000 in
/-- Field-0 (nonce) value check (`AB+92 → 552/152`): load len+offset, strip leading
    zeros, `bltu 8, sigLen`.  Fail edge is value overflow (`¬nonceValueOk`); continue
    carries `x6 = sigLen` and `x28 = listBase + significantOff`. -/
theorem adNonceLenCheck
    (listBase offset len : Word) (bytes : List (BitVec 8))
    (v5old v6old v7old v28old v29old : Word)
    (halign : listBase.toNat % 8 = 0)
    (hbound : offset.toNat + len.toNat ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (_hoff : listBase.toNat + offset.toNat < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true) :
    let o0 := offset.toNat
    let n := len.toNat
    let sig := n - nlzWin bytes o0 n
    let sigPtr := listBase + BitVec.ofNat 64 (o0 + nlzWin bytes o0 n)
    cpsBranchWithin (6 * n + 12) (AB + 92) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
       bytesRegion listBase bytes)
      (AB + 552)
        (((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) **
         ((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
         ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
         bytesRegion listBase bytes **
         ⌜BitVec.ult (8 : Word) (BitVec.ofNat 64 sig)⌝)
      (AB + 152)
        (((.x7 : Reg) ↦ᵣ (8 : Word)) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) **
         ((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
         ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
         bytesRegion listBase bytes **
         ⌜¬ BitVec.ult (8 : Word) (BitVec.ofNat 64 sig)⌝) := by
  intro o0 n sig sigPtr
  have hlenEq : BitVec.ofNat 64 n = len := ad_len_eq_ofNat len
  have hoffEq : listBase + offset = listBase + BitVec.ofNat 64 o0 := ad_add_base_off listBase offset
  have hoff0 : listBase + offset = listBase + BitVec.ofNat 64 (o0 + 0) := by
    rw [Nat.add_zero]; exact hoffEq
  -- la len
  have hla := adLaLenX5_92 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hla
  -- ld x6
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 100) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 100 : Word) + 4 = AB + 104 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 100) accountDecode_prog 25
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hlde
  -- la offset
  have hlao := adLaOffX5_104 adLengthAddr
  have hlaof := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hlao
  -- ld x28
  have hldo := ld_spec_gen_within .x28 .x5 adOffsetAddr v28old offset (0 : BitVec 12)
    (AB + 112) (by decide)
  rw [show adOffsetAddr + signExtend12 (0 : BitVec 12) = adOffsetAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 112 : Word) + 4 = AB + 116 from by bv_omega] at hldo
  have hldoe := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 112) accountDecode_prog 28
        (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hldo)
  have hldof := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** bytesRegion listBase bytes)
    (by pcFreeR) hldoe
  -- add x28, x8, x28
  have hadd := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset (AB + 116) (by decide)
  rw [show (AB + 116 : Word) + 4 = AB + 120 from by bv_omega] at hadd
  have hadde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 116) accountDecode_prog 29
        (.ADD .x28 .x8 .x28) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hadd)
  have haddf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ v7old) **
     ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hadde
  -- strip (frame keeps x5/x7/x8 + cells)
  have hstrip0 := adNonceStrip listBase bytes o0 n 0 v29old halign (by omega) hover hvalid
  have hstrip := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset))
    (by pcFreeR) hstrip0
  -- li x7, 8
  have hli := li_spec_gen_within .x7 v7old (8 : Word) (AB + 144) (by decide)
  rw [show (AB + 144 : Word) + 4 = AB + 148 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 144) accountDecode_prog 36
        (.LI .x7 (8 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
     bytesRegion listBase bytes)
    (by pcFreeR) hlie
  -- compose straight-line through strip
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlaf hldf
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hlaof
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 hldof
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 haddf
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      -- Rewrite only the x6/x28 register atoms; leave `adLengthAddr ↦ₘ len` alone.
      rw [show ((.x6 : Reg) ↦ᵣ len) = ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) from by
        rw [hlenEq]] at hp
      rw [show ((.x28 : Reg) ↦ᵣ (listBase + offset)) =
            ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o0 + 0))) from by
        rw [hoff0]] at hp
      xperm_chunked hp) s4 hstrip
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      -- strip post uses `(o0 + 0 + nlz)` / `nlz at (o0+0)`; align to sig/sigPtr.
      rw [show ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - nlzWin bytes (o0 + 0) n)) =
            ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) from by
        simp only [sig, o0, n, Nat.add_zero]] at hp
      rw [show ((.x28 : Reg) ↦ᵣ
            (listBase + BitVec.ofNat 64 (o0 + 0 + nlzWin bytes (o0 + 0) n))) =
            ((.x28 : Reg) ↦ᵣ sigPtr) from by
        simp only [sigPtr, o0, n, Nat.add_zero]] at hp
      xperm_chunked hp) s5 hlif
  -- bltu
  have hbltu := bltu_spec_gen_within .x7 .x6 (404 : BitVec 13) (8 : Word)
    (BitVec.ofNat 64 sig) (AB + 148)
  rw [show (AB + 148 : Word) + signExtend13 (404 : BitVec 13) = AB + 552 from by
    rw [show signExtend13 (404 : BitVec 13) = (404 : Word) from by decide]; bv_omega,
    show (AB + 148 : Word) + 4 = AB + 152 from by bv_omega] at hbltu
  have hbltue := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 148) accountDecode_prog 37
        (.BLTU .x7 .x6 (404 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbltu)
  have hbltuf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hbltue
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_chunked hp) sStraight hbltuf
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) (fun _ hq => by xperm_chunked hq) hcomposed)

#print axioms adNonceLenCheck

set_option maxRecDepth 8000 in
/-- Field-1 (balance) value check (`AB+224 → 552/284`): load len+offset, strip,
    `bltu 32, sigLen`. -/
theorem adBalLenCheck
    (listBase offset len : Word) (bytes : List (BitVec 8))
    (v5old v6old v7old v28old v29old : Word)
    (halign : listBase.toNat % 8 = 0)
    (hbound : offset.toNat + len.toNat ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (_hoff : listBase.toNat + offset.toNat < 2 ^ 64)
    (hvalid : ∀ j, j < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 j) = true) :
    let o0 := offset.toNat
    let n := len.toNat
    let sig := n - nlzWin bytes o0 n
    let sigPtr := listBase + BitVec.ofNat 64 (o0 + nlzWin bytes o0 n)
    cpsBranchWithin (6 * n + 12) (AB + 224) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
       bytesRegion listBase bytes)
      (AB + 552)
        (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) **
         ((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
         ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
         bytesRegion listBase bytes **
         ⌜BitVec.ult (32 : Word) (BitVec.ofNat 64 sig)⌝)
      (AB + 284)
        (((.x7 : Reg) ↦ᵣ (32 : Word)) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) **
         ((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
         ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
         (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
         bytesRegion listBase bytes **
         ⌜¬ BitVec.ult (32 : Word) (BitVec.ofNat 64 sig)⌝) := by
  intro o0 n sig sigPtr
  have hlenEq : BitVec.ofNat 64 n = len := ad_len_eq_ofNat len
  have hoffEq : listBase + offset = listBase + BitVec.ofNat 64 o0 := ad_add_base_off listBase offset
  have hoff0 : listBase + offset = listBase + BitVec.ofNat 64 (o0 + 0) := by
    rw [Nat.add_zero]; exact hoffEq
  have hla := adLaLenX5_200 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 232) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 232 : Word) + 4 = AB + 236 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 232) accountDecode_prog 58
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR
    (((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hlde
  have hlao := adLaOffX5_236 adLengthAddr
  have hlaof := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ v28old) ** ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hlao
  have hldo := ld_spec_gen_within .x28 .x5 adOffsetAddr v28old offset (0 : BitVec 12)
    (AB + 244) (by decide)
  rw [show adOffsetAddr + signExtend12 (0 : BitVec 12) = adOffsetAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 244 : Word) + 4 = AB + 248 from by bv_omega] at hldo
  have hldoe := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 244) accountDecode_prog 61
        (.LD .x28 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hldo)
  have hldof := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** bytesRegion listBase bytes)
    (by pcFreeR) hldoe
  have hadd := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset (AB + 248) (by decide)
  rw [show (AB + 248 : Word) + 4 = AB + 252 from by bv_omega] at hadd
  have hadde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 248) accountDecode_prog 62
        (.ADD .x28 .x8 .x28) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hadd)
  have haddf := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ v7old) **
     ((.x29 : Reg) ↦ᵣ v29old) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hadde
  have hstrip0 := adBalStrip listBase bytes o0 n 0 v29old halign (by omega) hover hvalid
  have hstrip := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x7 : Reg) ↦ᵣ v7old) ** ((.x8 : Reg) ↦ᵣ listBase) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset))
    (by pcFreeR) hstrip0
  have hli := li_spec_gen_within .x7 v7old (32 : Word) (AB + 276) (by decide)
  rw [show (AB + 276 : Word) + 4 = AB + 280 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 276) accountDecode_prog 69
        (.LI .x7 (32 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) **
     ((.x8 : Reg) ↦ᵣ listBase) ** ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 **
     ((.x0 : Reg) ↦ᵣ (0 : Word)) ** (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) **
     bytesRegion listBase bytes)
    (by pcFreeR) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) hlaf hldf
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 hlaof
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 hldof
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 haddf
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      rw [show ((.x6 : Reg) ↦ᵣ len) = ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) from by
        rw [hlenEq]] at hp
      rw [show ((.x28 : Reg) ↦ᵣ (listBase + offset)) =
            ((.x28 : Reg) ↦ᵣ (listBase + BitVec.ofNat 64 (o0 + 0))) from by
        rw [hoff0]] at hp
      xperm_chunked hp) s4 hstrip
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
      rw [show ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n - nlzWin bytes (o0 + 0) n)) =
            ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 sig) from by
        simp only [sig, o0, n, Nat.add_zero]] at hp
      rw [show ((.x28 : Reg) ↦ᵣ
            (listBase + BitVec.ofNat 64 (o0 + 0 + nlzWin bytes (o0 + 0) n))) =
            ((.x28 : Reg) ↦ᵣ sigPtr) from by
        simp only [sigPtr, o0, n, Nat.add_zero]] at hp
      xperm_chunked hp) s5 hlif
  have hbltu := bltu_spec_gen_within .x7 .x6 (272 : BitVec 13) (32 : Word)
    (BitVec.ofNat 64 sig) (AB + 280)
  rw [show (AB + 280 : Word) + signExtend13 (272 : BitVec 13) = AB + 552 from by
    rw [show signExtend13 (272 : BitVec 13) = (272 : Word) from by decide]; bv_omega,
    show (AB + 280 : Word) + 4 = AB + 284 from by bv_omega] at hbltu
  have hbltue := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 280) accountDecode_prog 70
        (.BLTU .x7 .x6 (272 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbltu)
  have hbltuf := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
     ((.x28 : Reg) ↦ᵣ sigPtr) ** regOwn .x29 ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
     (adLengthAddr ↦ₘ len) ** (adOffsetAddr ↦ₘ offset) ** bytesRegion listBase bytes)
    (by pcFreeR) hbltue
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_chunked hp) sStraight hbltuf
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsBranchWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) (fun _ hq => by xperm_chunked hq) hcomposed)

#print axioms adBalLenCheck

set_option maxRecDepth 8000 in
/-- Field-2 (storage_root) length check [81]-[85] (`AB+324 → 544/344`): `bne len, 32`.

    ⚠️ Post-#11483 the taken edge is **no longer the failure block**.  `len ≠ 32`
    now lands on the zero-length dispatch at `AB+544` (`adRootZeroDispatch`),
    which folds `len = 0` to `EMPTY_TRIE_ROOT` and only then falls through to the
    shared failure block.  So this theorem no longer says "len ≠ 32 → fail"; the
    guest's field-2 length contract is "len ∉ {0, 32} → fail", and it takes both
    this branch and `adRootZeroDispatch` to state it. -/
theorem adRootLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (AB + 372) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
      (AB + 592)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len ≠ (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
      (AB + 392)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len = (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len)) := by
  have hla := adLaLenX5_324 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 380) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 380 : Word) + 4 = AB + 384 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 380) accountDecode_prog 95
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ v7old) pcFree_regIs hlde
  have hli := li_spec_gen_within .x7 v7old (32 : Word) (AB + 384) (by decide)
  rw [show (AB + 384 : Word) + 4 = AB + 388 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 384) accountDecode_prog 96
        (.LI .x7 (32 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  have hbne := bne_spec_gen_within .x6 .x7 (204 : BitVec 13) len (32 : Word) (AB + 388)
  rw [show (AB + 388 : Word) + signExtend13 (204 : BitVec 13) = AB + 592 from by
    rw [show signExtend13 (204 : BitVec 13) = (204 : Word) from by decide]; bv_omega,
    show (AB + 388 : Word) + 4 = AB + 392 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 388) accountDecode_prog 97
        (.BNE .x6 .x7 (204 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbne)
  have hbnef := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbnee
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbnef
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms adRootLenCheck

set_option maxRecDepth 8000 in
/-- Field-3 (code_hash) length check [107]-[111] (`AB+428 → 596/448`): `bne len, 32`.

    ⚠️ Post-#11483 the taken edge is **no longer the failure block** — see
    `adRootLenCheck`.  `len ≠ 32` lands on `adCodeZeroDispatch` (`AB+596`), which
    folds `len = 0` to `EMPTY_CODE_HASH` before failing for any other length. -/
theorem adCodeLenCheck (v5old v6old v7old len : Word) :
    cpsBranchWithin 5 (AB + 476) fullCode
      (((.x5 : Reg) ↦ᵣ v5old) ** ((.x6 : Reg) ↦ᵣ v6old) **
       ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
      (AB + 644)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len ≠ (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
      (AB + 496)
        ((((.x6 : Reg) ↦ᵣ len) ** ((.x7 : Reg) ↦ᵣ (32 : Word)) ** ⌜len = (32 : Word)⌝) **
         ((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len)) := by
  have hla := adLaLenX5_428 v5old
  have hlaf := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6old) ** ((.x7 : Reg) ↦ᵣ v7old) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hla
  have hld := ld_spec_gen_within .x6 .x5 adLengthAddr v6old len (0 : BitVec 12)
    (AB + 484) (by decide)
  rw [show adLengthAddr + signExtend12 (0 : BitVec 12) = adLengthAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 484 : Word) + 4 = AB + 488 from by bv_omega] at hld
  have hlde := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 484) accountDecode_prog 121
        (.LD .x6 .x5 (0 : BitVec 12)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hld)
  have hldf := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ v7old) pcFree_regIs hlde
  have hli := li_spec_gen_within .x7 v7old (32 : Word) (AB + 488) (by decide)
  rw [show (AB + 488 : Word) + 4 = AB + 492 from by bv_omega] at hli
  have hlie := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 488) accountDecode_prog 122
        (.LI .x7 (32 : Word)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hli)
  have hlif := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** ((.x6 : Reg) ↦ᵣ len) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hlie
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaf hldf
  have sStraight := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 hlif
  have hbne := bne_spec_gen_within .x6 .x7 (152 : BitVec 13) len (32 : Word) (AB + 492)
  rw [show (AB + 492 : Word) + signExtend13 (152 : BitVec 13) = AB + 644 from by
    rw [show signExtend13 (152 : BitVec 13) = (152 : Word) from by decide]; bv_omega,
    show (AB + 492 : Word) + 4 = AB + 496 from by bv_omega] at hbne
  have hbnee := cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 492) accountDecode_prog 123
        (.BNE .x6 .x7 (152 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbne)
  have hbnef := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ adLengthAddr) ** (adLengthAddr ↦ₘ len))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) hbnee
  have hcomposed := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) sStraight hbnef
  exact cpsBranchWithin_mono_nSteps (by omega) hcomposed

#print axioms adCodeLenCheck

/-! ## The zero-length hash dispatch (GH #11483)

    `witness_state.py:114-119` folds a **zero-length** `storage_root` /
    `code_hash` field to `EMPTY_TRIE_ROOT` / `EMPTY_CODE_HASH` rather than
    rejecting it.  The guest mirrors that with a second-level dispatch appended
    after the epilogue: each exact-32 `BNE` above now targets a `BEQ x6, x0`
    arm whose **taken** edge stores the 32-byte constant and rejoins the field's
    normal continuation, and whose **fall-through** is a `JAL` back into the
    shared failure block at `AB+504`.

    Consequently the field-2/3 length contract is no longer expressible as one
    branch: `adRootLenCheck ⨾ adRootZeroDispatch` together say
    "`len ∉ {0, 32}` → fail", which is what the program now does. -/

set_option maxRecDepth 8000 in
/-- Field-2 zero-length dispatch [136] (`AB+544 → 552/548`): `beq len, x0`.
    Taken (`len = 0`) enters the `EMPTY_TRIE_ROOT` store at `AB+552`;
    fall-through (`len ∉ {0, 32}`, given `adRootLenCheck`'s taken edge) is the
    `JAL` at `AB+548` into the shared failure block. -/
theorem adRootZeroDispatch (len : Word) :
    cpsBranchWithin 1 (AB + 592) fullCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (AB + 600)
        (((.x6 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜len = (0 : Word)⌝)
      (AB + 596)
        (((.x6 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜len ≠ (0 : Word)⌝) := by
  have hbeq := beq_spec_gen_within .x6 .x0 (8 : BitVec 13) len (0 : Word) (AB + 592)
  rw [show (AB + 592 : Word) + signExtend13 (8 : BitVec 13) = AB + 600 from by
    rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega,
    show (AB + 592 : Word) + 4 = AB + 596 from by bv_omega] at hbeq
  exact cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 592) accountDecode_prog 148
        (.BEQ .x6 .x0 (8 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbeq)

#print axioms adRootZeroDispatch

set_option maxRecDepth 8000 in
/-- Field-2 zero-dispatch fall-through [137] (`AB+548 → AB+504`): the `JAL` into
    the shared failure block, taken when the `storage_root` field length is
    neither 0 nor 32.  This is where the pre-#11483 `adRootLenCheck` taken edge
    used to land directly. -/
theorem adRootFoldFailJal :
    cpsTripleWithin 1 (AB + 596) (AB + 552) fullCode empAssertion empAssertion := by
  have hjal := jal_x0_spec_gen_within (-44 : BitVec 21) (AB + 596)
  rw [show (AB + 596 : Word) + signExtend21 (-44 : BitVec 21) = AB + 552 from by
    rw [show signExtend21 (-44 : BitVec 21) = (-44 : Word) from by decide]; bv_omega] at hjal
  exact cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 596) accountDecode_prog 149
        (.JAL .x0 (-44 : BitVec 21)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hjal)

#print axioms adRootFoldFailJal

set_option maxRecDepth 8000 in
/-- Field-3 zero-length dispatch [149] (`AB+596 → 604/600`): `beq len, x0`.
    Taken (`len = 0`) enters the `EMPTY_CODE_HASH` store at `AB+604`;
    fall-through is the `JAL` at `AB+600` into the shared failure block. -/
theorem adCodeZeroDispatch (len : Word) :
    cpsBranchWithin 1 (AB + 644) fullCode
      (((.x6 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (AB + 652)
        (((.x6 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜len = (0 : Word)⌝)
      (AB + 648)
        (((.x6 : Reg) ↦ᵣ len) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ⌜len ≠ (0 : Word)⌝) := by
  have hbeq := beq_spec_gen_within .x6 .x0 (8 : BitVec 13) len (0 : Word) (AB + 644)
  rw [show (AB + 644 : Word) + signExtend13 (8 : BitVec 13) = AB + 652 from by
    rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]; bv_omega,
    show (AB + 644 : Word) + 4 = AB + 648 from by bv_omega] at hbeq
  exact cpsBranchWithin_extend_code ad_mono
    (cpsBranchWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 644) accountDecode_prog 161
        (.BEQ .x6 .x0 (8 : BitVec 13)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hbeq)

#print axioms adCodeZeroDispatch

set_option maxRecDepth 8000 in
/-- Field-3 zero-dispatch fall-through [150] (`AB+600 → AB+504`): the `JAL` into
    the shared failure block, for a `code_hash` length that is neither 0 nor 32. -/
theorem adCodeFoldFailJal :
    cpsTripleWithin 1 (AB + 648) (AB + 552) fullCode empAssertion empAssertion := by
  have hjal := jal_x0_spec_gen_within (-96 : BitVec 21) (AB + 648)
  rw [show (AB + 648 : Word) + signExtend21 (-96 : BitVec 21) = AB + 552 from by
    rw [show signExtend21 (-96 : BitVec 21) = (-96 : Word) from by decide]; bv_omega] at hjal
  exact cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 648) accountDecode_prog 162
        (.JAL .x0 (-96 : BitVec 21)) (by bv_omega) (by rw [ad_length]; decide)
        rfl (by rw [ad_length]; decide)) hjal)

#print axioms adCodeFoldFailJal

end EvmAsm.Codegen.AccountDecodeSpec
