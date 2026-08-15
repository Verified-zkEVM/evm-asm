/-
  `accountDecode_prog` caller-contract composition, part 1 — the K20 content
  bound and the small glue leaves that connect the length checks / calls to
  the per-field materialisers and the status tails.

  Ported / mirrored from `WithdrawalDecodeSpec` (the `strictNthItem_content_le`
  content span bound and the `wdSuccessTail`/`wdFailTail` status tails).

    * `strictNthItem_content_le` / `adSuccessContentBound` — a K20 `Success`'s
      selected content span (offset + length) fits inside the declared list
      length.
    * `adNonceSetup` [28]-[32] — `la ad_offset ; ld ; add x28=listBase+offset ;
      li x7,0`, feeding `adNonceLoop`.
    * `adRootCopySetup` [86]-[89] / `adCodeCopySetup` [112]-[115] — the fixed-32
      copy source-cursor setups (`la ad_offset ; ld ; add x28=listBase+offset`).
    * `adNonceStore` [40] — `sd x18, x7`, storing the accumulated LE u64 nonce.
    * `adSuccessTail` [124]-[125] / `adFailTail` [126] — the `a0 := 0`/`a0 := 1`
      status writes converging on the epilogue entry (`AB+508`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountDecodeBalanceSetup
import EvmAsm.Rv64.RLP.WalkItemDeterminism

namespace EvmAsm.Codegen.AccountDecodeSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

/-! ## K20 content-span bound (all four fields)

    The selected item's content span (offset + length) fits inside the declared
    list window `endOff`.  Induction on the `StrictNthItem` chain: each
    non-final decode strictly advances the cursor but stays `≤ endOff`
    (`rlpItemDecode_advance`); the final decode's span is bounded by
    `rlpItemDecode_field0_content_span`.  Mirrors
    `WithdrawalDecodeSpec.strictNthItem_content_le`. -/

open EvmAsm.Codegen.RlpListNthItemSAsm in
theorem strictNthItem_content_le {bytes : List (BitVec 8)} {base : Word}
    {endOff : Nat} : ∀ {index cursorOff : Nat} {next len : Word},
    StrictNthItem bytes base (base + BitVec.ofNat 64 endOff) index cursorOff next len →
    cursorOff ≤ endOff →
    base.toNat + endOff + 9 < 2 ^ 64 →
    (next - len - base).toNat + len.toNat ≤ endOff := by
  intro index cursorOff next len h
  induction h with
  | zero off n l hitem =>
      intro hcursor hover
      exact (EvmAsm.Rv64.RLP.rlpItemDecode_field0_content_span hitem hcursor hover).2.2
  | succ idx off n l fn fl hitem hrest ih =>
      intro hcursor hover
      have hadv := EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hitem hcursor hover
      exact ih hadv.2.2 hover

#print axioms strictNthItem_content_le

open EvmAsm.Codegen.RlpListNthItemSAsm in
/-- From a K20 `Success` (any index), the selected content offset plus length
    fits inside the declared list length.  Mirrors `wdSuccessContentBound`
    (generalised over the field index). -/
theorem adSuccessContentBound (bytes : List (BitVec 8)) (listBase : Word)
    (listLen index : Nat) (offset len' : Word)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hsucc : EvmAsm.Codegen.RlpListNthItemSAsm.Success bytes listBase listLen index offset len') :
    offset.toNat + len'.toNat ≤ listLen := by
  obtain ⟨cursorOff, endPtr, next, hpay, hnth, hoff⟩ := hsucc
  have hend := hpay.end_eq
  have hcur := hpay.cursor_le
  subst hend
  subst hoff
  exact strictNthItem_content_le hnth hcur (by omega)

#print axioms adSuccessContentBound

/-! ## `la x5, ad_offset` materialisers for the setup sites -/

/-- `la x5, ad_offset` at nonce setup [28]-[29] (`AB+112 → AB+120`). -/
private theorem adLaOffX5_112 (v : Word) :
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

/-- `la x5, ad_offset` at root copy setup [86]-[87] (`AB+344 → AB+352`). -/
private theorem adLaOffX5_344 (v : Word) :
    cpsTripleWithin 2 (AB + 392) (AB + 400) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 392)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 392)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 392) accountDecode_prog 98
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 392)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 396)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 392)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 396) accountDecode_prog 99
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 392)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 392) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 392 : Word) + 8 = AB + 400 from by bv_omega] at h
  exact h

/-- `la x5, ad_offset` at code copy setup [112]-[113] (`AB+448 → AB+456`). -/
private theorem adLaOffX5_448 (v : Word) :
    cpsTripleWithin 2 (AB + 496) (AB + 504) fullCode
      (.x5 ↦ᵣ v) (.x5 ↦ᵣ adOffsetAddr) := by
  have hau : ∀ a i, CodeReq.singleton (AB + 496)
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 496)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 496) accountDecode_prog 124
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.ad_offset (GuestAddrs.account_decode + 496)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have had : ∀ a i, CodeReq.singleton (AB + 500)
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 496)))
        a = some i → fullCode a = some i := fun a i hi => ad_mono a i
    (CodeReq.ofProg_mem_at AB (AB + 500) accountDecode_prog 125
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.ad_offset (GuestAddrs.account_decode + 496)))
      (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide) a i hi)
  have h := la_materialize_within .x5 v (AB + 496) adOffsetAddr (by decide) (by decide) hau had
  rw [show (AB + 496 : Word) + 8 = AB + 504 from by bv_omega] at h
  exact h

/-! ## Glue leaf: nonce loop setup (`AB+152 → AB+156`) -/

set_option maxRecDepth 8000 in
/-- After the value-check continue edge, x28 already holds the significant-byte
    cursor; only `li x7, 0` remains before the nonce accum loop (`AB+152 → 156`). -/
theorem adNonceSetup (v7 : Word) :
    cpsTripleWithin 1 (AB + 152) (AB + 156) fullCode
      ((.x7 : Reg) ↦ᵣ v7)
      ((.x7 : Reg) ↦ᵣ (0 : Word)) := by
  have h32 := li_spec_gen_within .x7 v7 (0 : Word) (AB + 152) (by decide)
  rw [show (AB + 152 : Word) + 4 = AB + 156 from by bv_omega] at h32
  exact cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 152) accountDecode_prog 38 (.LI .x7 (0 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h32)

#print axioms adNonceSetup

/-! ## Glue leaf: nonce store [40] (`AB+160 → AB+164`) -/

set_option maxRecDepth 8000 in
/-- Nonce store [40] (`AB+160 → AB+164`): `sd x18, x7` — write the accumulated
    big-endian u64 (as a little-endian dword) into the 8-byte nonce slot. -/
theorem adNonceStore (nonceOut nonceVal oldVal : Word) :
    cpsTripleWithin 1 (AB + 184) (AB + 188) fullCode
      (((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x7 : Reg) ↦ᵣ nonceVal) ** (nonceOut ↦ₘ oldVal))
      (((.x18 : Reg) ↦ᵣ nonceOut) ** ((.x7 : Reg) ↦ᵣ nonceVal) ** (nonceOut ↦ₘ nonceVal)) := by
  have h := sd_spec_gen_within .x18 .x7 nonceOut nonceVal oldVal (0 : BitVec 12) (AB + 184)
  rw [show nonceOut + signExtend12 (0 : BitVec 12) = nonceOut from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 184 : Word) + 4 = AB + 188 from by bv_omega] at h
  exact cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 184) accountDecode_prog 46 (.SD .x18 .x7 (0 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h)

#print axioms adNonceStore

/-! ## Glue leaves: the fixed-32 copy source-cursor setups -/

set_option maxRecDepth 8000 in
/-- Root copy source-cursor setup [86]-[89] (`AB+344 → AB+360`):
    `la x5,ad_offset ; ld x28 ; add x28=listBase+offset`.  Feeds `adCopyLoop`. -/
theorem adRootCopySetup (listBase offset v5 v28 : Word) :
    cpsTripleWithin 4 (AB + 392) (AB + 408) fullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x28 : Reg) ↦ᵣ v28) ** (adOffsetAddr ↦ₘ offset))
      (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x28 : Reg) ↦ᵣ (listBase + offset)) ** (adOffsetAddr ↦ₘ offset)) := by
  have h86 := adLaOffX5_344 v5
  have h86f := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x28 : Reg) ↦ᵣ v28) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h86
  have h88 := ld_spec_gen_within .x28 .x5 adOffsetAddr v28 offset (0 : BitVec 12)
    (AB + 400) (by decide)
  rw [show adOffsetAddr + signExtend12 (0 : BitVec 12) = adOffsetAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 400 : Word) + 4 = AB + 404 from by bv_omega] at h88
  have h88e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 400) accountDecode_prog 100 (.LD .x28 .x5 (0 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h88)
  have h88f := cpsTripleWithin_frameR ((.x8 : Reg) ↦ᵣ listBase) pcFree_regIs h88e
  have h89 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset (AB + 404) (by decide)
  rw [show (AB + 404 : Word) + 4 = AB + 408 from by bv_omega] at h89
  have h89e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 404) accountDecode_prog 101 (.ADD .x28 .x8 .x28)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h89)
  have h89f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h89e
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h86f h88f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 h89f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c2

#print axioms adRootCopySetup

set_option maxRecDepth 8000 in
/-- Code copy source-cursor setup [112]-[115] (`AB+448 → AB+464`):
    `la x5,ad_offset ; ld x28 ; add x28=listBase+offset`.  Feeds `adCopyLoop`. -/
theorem adCodeCopySetup (listBase offset v5 v28 : Word) :
    cpsTripleWithin 4 (AB + 496) (AB + 512) fullCode
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x28 : Reg) ↦ᵣ v28) ** (adOffsetAddr ↦ₘ offset))
      (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** ((.x8 : Reg) ↦ᵣ listBase) **
       ((.x28 : Reg) ↦ᵣ (listBase + offset)) ** (adOffsetAddr ↦ₘ offset)) := by
  have h112 := adLaOffX5_448 v5
  have h112f := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ listBase) ** ((.x28 : Reg) ↦ᵣ v28) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h112
  have h114 := ld_spec_gen_within .x28 .x5 adOffsetAddr v28 offset (0 : BitVec 12)
    (AB + 504) (by decide)
  rw [show adOffsetAddr + signExtend12 (0 : BitVec 12) = adOffsetAddr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega,
    show (AB + 504 : Word) + 4 = AB + 508 from by bv_omega] at h114
  have h114e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 504) accountDecode_prog 126 (.LD .x28 .x5 (0 : BitVec 12))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h114)
  have h114f := cpsTripleWithin_frameR ((.x8 : Reg) ↦ᵣ listBase) pcFree_regIs h114e
  have h115 := add_spec_gen_rd_eq_rs2_within .x28 .x8 listBase offset (AB + 508) (by decide)
  rw [show (AB + 508 : Word) + 4 = AB + 512 from by bv_omega] at h115
  have h115e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 508) accountDecode_prog 127 (.ADD .x28 .x8 .x28)
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h115)
  have h115f := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ adOffsetAddr) ** (adOffsetAddr ↦ₘ offset))
    (by repeat' first | exact pcFree_regIs | exact pcFree_memIs | apply pcFree_sepConj) h115e
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) h112f h114f
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 h115f
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c2

#print axioms adCodeCopySetup

/-! ## Status tails [124]-[126] -/

set_option maxRecDepth 8000 in
/-- Success tail [124]-[125] (`AB+496 → AB+508`): `li a0,0 ; jal +8` — set the
    success status and jump past the failure `li` to the epilogue entry.
    Generic over the untouched frame `G`. -/
theorem adSuccessTail (v10old : Word) (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 2 (AB + 544) (AB + 556) fullCode
      (((.x10 : Reg) ↦ᵣ v10old) ** G)
      (((.x10 : Reg) ↦ᵣ (0 : Word)) ** G) := by
  have h0 := li_spec_gen_within .x10 v10old (0 : Word) (AB + 544) (by decide)
  rw [show (AB + 544 : Word) + 4 = AB + 548 from by bv_omega] at h0
  have h0e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 544) accountDecode_prog 136 (.LI .x10 (0 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h0)
  have h1 := jal0_spec_pcFree (P := ((.x10 : Reg) ↦ᵣ (0 : Word)) ** G) (8 : BitVec 21)
    (AB + 548) (pcFree_sepConj pcFree_regIs hG)
  rw [show AB + 548 + signExtend21 (8 : BitVec 21) = AB + 556 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at h1
  have h1e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 548) accountDecode_prog 137 (.JAL .x0 (8 : BitVec 21))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h1)
  have f0 := cpsTripleWithin_frameR G hG h0e
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) f0 h1e

#print axioms adSuccessTail

set_option maxRecDepth 8000 in
/-- Failure tail [126] (`AB+504 → AB+508`): `li a0,1` then fall through to the
    epilogue entry.  Generic over the untouched frame `G`. -/
theorem adFailTail (v10old : Word) (G : Assertion) (hG : G.pcFree) :
    cpsTripleWithin 1 (AB + 552) (AB + 556) fullCode
      (((.x10 : Reg) ↦ᵣ v10old) ** G)
      (((.x10 : Reg) ↦ᵣ (1 : Word)) ** G) := by
  have h0 := li_spec_gen_within .x10 v10old (1 : Word) (AB + 552) (by decide)
  rw [show (AB + 552 : Word) + 4 = AB + 556 from by bv_omega] at h0
  have h0e := cpsTripleWithin_extend_code ad_mono
    (cpsTripleWithin_extend_code
      (CodeReq.ofProg_mem_at AB (AB + 552) accountDecode_prog 138 (.LI .x10 (1 : Word))
        (by bv_omega) (by rw [ad_length]; decide) rfl (by rw [ad_length]; decide)) h0)
  exact cpsTripleWithin_frameR G hG h0e

#print axioms adFailTail

end EvmAsm.Codegen.AccountDecodeSpec
