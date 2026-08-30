/-
  EvmAsm.Codegen.Proofs.DCodeLeafFlatEntries

  Flat whole-routine contracts at the linked guest entries for the four
  remaining proof-first (DCode) leaves (#13089): `modexp_iszero`,
  `sender_post_nonce_consistent`, `edd_be32_eq`, and `edd_memcpy` — the
  same census gap #13071 closed for `sg_validate_fixed_list`.  Each is
  the leaf's base-generic `retSpec` with the caller's exposed-register
  atoms packed into / unpacked from the callee's `asrtM` register file.
  Lives outside the SAsm files so the (rebuild-heavy) `GuestAddrs`
  dependency stays out of the derivations' import cones.
-/

import EvmAsm.Codegen.Programs.ModexpIszeroSAsm
import EvmAsm.Codegen.Programs.SenderPostNonceConsistentSAsm
import EvmAsm.Codegen.Programs.ExtractDepositData
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.DCodeLeafFlatEntries

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics

/-! ## Exposed-register bookkeeping (shared by the four entries) -/

/-- The exposed registers except `a0`. -/
def leafScr14 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The exposed registers except `a0`/`a1`. -/
def leafScr13 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

/-- The exposed registers except `a0`/`a1`/`a2`. -/
def leafScr12 : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem leaf_split_1 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** regAtomsOf vf leafScr14) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [leafScr14, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem leaf_split_2 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** ((.x11 : Reg) ↦ᵣ vf .x11) **
          regAtomsOf vf leafScr13) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [leafScr13, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem leaf_split_3 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = (((.x10 : Reg) ↦ᵣ vf .x10) ** ((.x11 : Reg) ↦ᵣ vf .x11) **
          ((.x12 : Reg) ↦ᵣ vf .x12) ** regAtomsOf vf leafScr12) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [leafScr12, regAtomsOf_cons, regAtomsOf_nil]
  xperm

/-- The two-pin callee-entry register file (`a0`, `a1`). -/
private def rf2 (a b : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x10 then a else if r = .x11 then b else vf r

/-- The three-pin callee-entry register file (`a0`, `a1`, `a2`). -/
private def rf3 (a b c : Word) (vf : Reg → Word) : RegFile :=
  fun r => if r = .x10 then a else if r = .x11 then b
    else if r = .x12 then c else vf r

private theorem rf2_get10 (a b : Word) (vf : Reg → Word) :
    (rf2 a b vf).get .x10 = a := by
  rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
  exact if_pos rfl

private theorem rf2_get11 (a b : Word) (vf : Reg → Word) :
    (rf2 a b vf).get .x11 = b := by
  rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
  rw [rf2, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
  exact if_pos rfl

private theorem rf2_atoms (a b : Word) (vf : Reg → Word) :
    regAtomsOf (fun r => rf2 a b vf r) exposedRegs
      = (((.x10 : Reg) ↦ᵣ a) ** ((.x11 : Reg) ↦ᵣ b) **
          regAtomsOf vf leafScr13) := by
  rw [leaf_split_2,
    show rf2 a b vf .x10 = a from if_pos rfl,
    show rf2 a b vf .x11 = b from by
      rw [rf2, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl,
    regAtomsOf_congr (fun r => rf2 a b vf r) vf leafScr13
      (fun r hr => by
        show (if r = .x10 then a else if r = .x11 then b else vf r) = vf r
        rw [if_neg (fun hc => (by decide : (Reg.x10 : Reg) ∉ leafScr13)
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => (by decide : (Reg.x11 : Reg) ∉ leafScr13)
              (by rw [← hc]; exact hr))])]

private theorem rf3_get10 (a b c : Word) (vf : Reg → Word) :
    (rf3 a b c vf).get .x10 = a := by
  rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
  exact if_pos rfl

private theorem rf3_get11 (a b c : Word) (vf : Reg → Word) :
    (rf3 a b c vf).get .x11 = b := by
  rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
  rw [rf3, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
  exact if_pos rfl

private theorem rf3_get12 (a b c : Word) (vf : Reg → Word) :
    (rf3 a b c vf).get .x12 = c := by
  rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
  rw [rf3, if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
    if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
  exact if_pos rfl

private theorem rf3_atoms (a b c : Word) (vf : Reg → Word) :
    regAtomsOf (fun r => rf3 a b c vf r) exposedRegs
      = (((.x10 : Reg) ↦ᵣ a) ** ((.x11 : Reg) ↦ᵣ b) **
          ((.x12 : Reg) ↦ᵣ c) ** regAtomsOf vf leafScr12) := by
  rw [leaf_split_3,
    show rf3 a b c vf .x10 = a from if_pos rfl,
    show rf3 a b c vf .x11 = b from by
      rw [rf3, if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl,
    show rf3 a b c vf .x12 = c from by
      rw [rf3, if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl,
    regAtomsOf_congr (fun r => rf3 a b c vf r) vf leafScr12
      (fun r hr => by
        show (if r = .x10 then a else if r = .x11 then b
          else if r = .x12 then c else vf r) = vf r
        rw [if_neg (fun hc => (by decide : (Reg.x10 : Reg) ∉ leafScr12)
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => (by decide : (Reg.x11 : Reg) ∉ leafScr12)
              (by rw [← hc]; exact hr)),
          if_neg (fun hc => (by decide : (Reg.x12 : Reg) ∉ leafScr12)
              (by rw [← hc]; exact hr))])]

/-! ## `modexp_iszero` -/

abbrev MizB : Word := (GuestAddrs.modexp_iszero : Word)
abbrev mizCode : CodeReq :=
  CodeReq.ofProg MizB ModexpIszeroSAsm.modexpIszero_prog

set_option maxRecDepth 1000000 in
private theorem miz_flatten (ptr b : Word) (bs : List (BitVec 8)) (n : Nat) :
    ((ModexpIszeroSAsm.mizDeriv ptr bs n).stmt.flatten b : List Instr)
      = ModexpIszeroSAsm.modexpIszero_prog := rfl

/-- ⭐ **`modexp_iszero` at its linked guest address.**  Entered with
    `a0` = limb pointer, `a1` = limb count `n` (≤ 256, `8n` bytes
    readable) and an aligned return address, it returns
    `a0 = mizOut ptr bs n` — `1` iff all `n` little-endian dwords are
    zero. -/
theorem modexpIszeroFlat_spec (ptr ret : Word) (bs : List (BitVec 8))
    (n : Nat)
    (hwf : (Region.mk ptr bs).wf)
    (hn : n ≤ 256) (hbs : 8 * n ≤ bs.length)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (ModexpIszeroSAsm.mizDeriv ptr bs n).stmt.steps
      MizB ret mizCode
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** regOwns leafScr13 **
        bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ ModexpIszeroSAsm.mizOut ptr bs n) **
        regOwns leafScr14 ** bytesRegion ptr bs) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns leafScr13 (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) ** bytesRegion ptr bs)
      (fun vf => ?_))
  have hret := ModexpIszeroSAsm.modexpIszero_retSpec ptr bs n MizB ret
    hwf halign
  rw [miz_flatten] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hret
  · refine sepConj_mono_right (fun h' hp' => ?_) h (by xperm_hyp hp :
      ((((.x1 : Reg) ↦ᵣ ret)) **
        ((((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          regAtomsOf vf leafScr13) ** bytesRegion ptr bs)) h)
    show (asrtOf RwRegion.empty _ ** bytesRegion ptr bs) h'
    refine sepConj_mono_left (fun h'' hp'' => ?_) h' hp'
    refine ⟨rf2 ptr (BitVec.ofNat 64 n) vf, [], empAssertion, rfl,
      pcFree_emp, ⟨⟨rf2_get10 _ _ _, rf2_get11 _ _ _, hn, hbs⟩, rfl⟩, ?_⟩
    rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      rf2_atoms]
    exact hp''
  · refine sepConj_mono_right (fun h' hq' => ?_) h hq
    have hq'' : (asrtOf RwRegion.empty _ ** bytesRegion ptr bs) h' := hq'
    have hfin := sepConj_mono_left (fun h'' hq2 => by
      obtain ⟨rf, ws, A, hws, -, ⟨h10, rfl⟩, hh⟩ := hq2
      obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
      rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        leaf_split_1,
        show rf .x10 = ModexpIszeroSAsm.mizOut ptr bs n from by
          rw [show rf .x10 = rf.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact h10] at hh
      exact sepConj_mono_right (regAtomsOf_to_regOwns _ _) h'' hh)
      h' hq''
    xperm_hyp hfin

/-! ## `sender_post_nonce_consistent` -/

abbrev SpncB : Word := (GuestAddrs.sender_post_nonce_consistent : Word)
abbrev spncCode : CodeReq :=
  CodeReq.ofProg SpncB SenderPostNonceConsistentSAsm.spnc_prog

set_option maxRecDepth 1000000 in
/-- Ghost-erasure hop: `flatten` drops the derivation's `Prop`-valued
    annotations, so the ghosts can be zeroed first (the one-step
    identity times out the elaborator's `whnf` at the default budget;
    the two hops each reduce within it). -/
private theorem spnc_flatten_ghost_free (rec b : Word)
    (bs : List (BitVec 8)) :
    ((SenderPostNonceConsistentSAsm.spncDeriv rec bs).stmt.flatten b
        : List Instr)
      = ((SenderPostNonceConsistentSAsm.spncDeriv 0 []).stmt.flatten b
        : List Instr) := rfl

set_option maxRecDepth 1000000 in
private theorem spnc_flatten_zero (b : Word) :
    ((SenderPostNonceConsistentSAsm.spncDeriv 0 []).stmt.flatten b
        : List Instr)
      = SenderPostNonceConsistentSAsm.spnc_prog := rfl

private theorem spnc_flatten (rec b : Word) (bs : List (BitVec 8)) :
    ((SenderPostNonceConsistentSAsm.spncDeriv rec bs).stmt.flatten b
        : List Instr)
      = SenderPostNonceConsistentSAsm.spnc_prog := by
  rw [spnc_flatten_ghost_free, spnc_flatten_zero]

/-- ⭐ **`sender_post_nonce_consistent` at its linked guest address.**
    Entered with `a0` = the 144-byte sender record and an aligned return
    address, it returns `a0 = spncOut bs` (0 consistent / 1 mismatch /
    2 skip). -/
theorem spncFlat_spec (rec ret : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk rec bs).wf)
    (hst : SenderPostNonceConsistentSAsm.spncStatic rec bs)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      (SenderPostNonceConsistentSAsm.spncDeriv rec bs).stmt.steps
      SpncB ret spncCode
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ rec) **
        regOwns leafScr14 ** bytesRegion rec bs)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ SenderPostNonceConsistentSAsm.spncOut bs) **
        regOwns leafScr14 ** bytesRegion rec bs) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns leafScr14 (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ rec) **
        bytesRegion rec bs)
      (fun vf => ?_))
  have hret := SenderPostNonceConsistentSAsm.spnc_retSpec rec bs hwf
    SpncB ret halign
  rw [spnc_flatten] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hret
  · refine sepConj_mono_right (fun h' hp' => ?_) h (by xperm_hyp hp :
      ((((.x1 : Reg) ↦ᵣ ret)) **
        ((((.x10 : Reg) ↦ᵣ rec) ** regAtomsOf vf leafScr14) **
          bytesRegion rec bs)) h)
    show (asrtOf RwRegion.empty _ ** bytesRegion rec bs) h'
    refine sepConj_mono_left (fun h'' hp'' => ?_) h' hp'
    refine ⟨fun r => if r = .x10 then rec else vf r, [], empAssertion,
      rfl, pcFree_emp,
      ⟨by
        show RegFile.get _ .x10 = rec
        rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
        exact if_pos rfl, hst, rfl⟩, ?_⟩
    rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      leaf_split_1,
      show (if (Reg.x10 : Reg) = .x10 then rec else vf .x10) = rec from
        if_pos rfl,
      regAtomsOf_congr (fun r => if r = .x10 then rec else vf r) vf
        leafScr14
        (fun r hr => by
          show (if r = .x10 then rec else vf r) = vf r
          rw [if_neg (fun hc => (by decide :
              (Reg.x10 : Reg) ∉ leafScr14) (by rw [← hc]; exact hr))])]
    exact hp''
  · refine sepConj_mono_right (fun h' hq' => ?_) h hq
    have hq'' : (asrtOf RwRegion.empty _ ** bytesRegion rec bs) h' := hq'
    have hfin := sepConj_mono_left (fun h'' hq2 => by
      obtain ⟨rf, ws, A, hws, -, ⟨h10, rfl⟩, hh⟩ := hq2
      obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
      rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        leaf_split_1,
        show rf .x10 = SenderPostNonceConsistentSAsm.spncOut bs from by
          rw [show rf .x10 = rf.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact h10] at hh
      exact sepConj_mono_right (regAtomsOf_to_regOwns _ _) h'' hh)
      h' hq''
    xperm_hyp hfin

/-! ## `edd_be32_eq` -/

abbrev EddBeB : Word := (GuestAddrs.edd_be32_eq : Word)
abbrev eddBeCode : CodeReq :=
  CodeReq.ofProg EddBeB EddBe32EqSAsm.eddBe32Eq_prog

/-- The `edd_be32_eq` derivation's generated `Stmt`, pinned explicitly
    (the direct `rfl` blows the kernel's recursion guard; see
    `ExtractDepositDataOkSpec.eddDeriv_stmt`). -/
private theorem eddBe_stmt (ptr : Word) (bs : List (BitVec 8)) (K : Word) :
    (EddBe32EqSAsm.eddDeriv ptr bs K).stmt
      = Stmt.seq (.block "init" [.LI .x5 (0 : Word)])
          (.retWhileHeaderBreak "zscan" (.block "hdr" [.LI .x6 (28 : Word)])
            (.bne .x5 .x6) 28
            (fun i rf ws A => EddBe32EqSAsm.eddInv ptr bs K i rf ws A)
            (.block "byte" [.ADD .x7 .x10 .x5, .LBU .x28 .x7 (0 : BitVec 12)])
            (.bne .x28 .x0)
            (.block "bump" [.ADDI .x5 .x5 (1 : BitVec 12)])
            [(EddBe32EqSAsm.eddStage, .bne .x6 .x11)]
            (.seq (.block "eq" [.LI .x10 (1 : Word)]) (.retJalr "eqr"))
            (.seq (.block "ne" [.LI .x10 (0 : Word)]) (.retJalr "ner"))) := rfl

set_option maxRecDepth 100000 in
private theorem eddBe_flatten (ptr b K : Word) (bs : List (BitVec 8)) :
    ((EddBe32EqSAsm.eddDeriv ptr bs K).stmt.flatten b : List Instr)
      = EddBe32EqSAsm.eddBe32Eq_prog := by
  rw [eddBe_stmt]; rfl

/-- ⭐ **`edd_be32_eq` at its linked guest address.**  Entered with
    `a0` = a 32-byte big-endian field pointer, `a1 = K` and an aligned
    return address, it returns `a0 = eddOut ptr bs K` — `1` iff the high
    28 bytes are zero and the trailing BE u32 equals `K`. -/
theorem eddBe32EqFlat_spec (ptr K ret : Word) (bs : List (BitVec 8))
    (hwf : (Region.mk ptr bs).wf)
    (hlen : 32 ≤ bs.length)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (EddBe32EqSAsm.eddDeriv ptr bs K).stmt.steps
      EddBeB ret eddBeCode
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ K) ** regOwns leafScr13 **
        bytesRegion ptr bs)
      (((.x1 : Reg) ↦ᵣ ret) **
        ((.x10 : Reg) ↦ᵣ EddBe32EqSAsm.eddOut ptr bs K) **
        regOwns leafScr14 ** bytesRegion ptr bs) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns leafScr13 (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ ptr) **
        ((.x11 : Reg) ↦ᵣ K) ** bytesRegion ptr bs)
      (fun vf => ?_))
  have hret := EddBe32EqSAsm.eddBe32Eq_retSpec ptr bs K EddBeB ret
    hwf halign
  rw [eddBe_flatten] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hret
  · refine sepConj_mono_right (fun h' hp' => ?_) h (by xperm_hyp hp :
      ((((.x1 : Reg) ↦ᵣ ret)) **
        ((((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ K) **
          regAtomsOf vf leafScr13) ** bytesRegion ptr bs)) h)
    show (asrtOf RwRegion.empty _ ** bytesRegion ptr bs) h'
    refine sepConj_mono_left (fun h'' hp'' => ?_) h' hp'
    refine ⟨rf2 ptr K vf, [], empAssertion, rfl, pcFree_emp,
      ⟨⟨rf2_get10 _ _ _, rf2_get11 _ _ _, hlen⟩, rfl⟩, ?_⟩
    rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      rf2_atoms]
    exact hp''
  · refine sepConj_mono_right (fun h' hq' => ?_) h hq
    have hq'' : (asrtOf RwRegion.empty _ ** bytesRegion ptr bs) h' := hq'
    have hfin := sepConj_mono_left (fun h'' hq2 => by
      obtain ⟨rf, ws, A, hws, -, ⟨h10, rfl⟩, hh⟩ := hq2
      obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero hws
      rw [bytesRegion_nil, sepConj_emp_right', sepConj_emp_right',
        regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        leaf_split_1,
        show rf .x10 = EddBe32EqSAsm.eddOut ptr bs K from by
          rw [show rf .x10 = rf.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact h10] at hh
      exact sepConj_mono_right (regAtomsOf_to_regOwns _ _) h'' hh)
      h' hq''
    xperm_hyp hfin

/-! ## `edd_memcpy` -/

abbrev EddMcB : Word := (GuestAddrs.edd_memcpy : Word)
abbrev eddMcCode : CodeReq :=
  CodeReq.ofProg EddMcB EddMemcpySAsm.eddMemcpy_prog

set_option maxRecDepth 1000000 in
private theorem eddMc_flatten (src dst b : Word) (bs ws : List (BitVec 8))
    (n : Nat) :
    ((EddMemcpySAsm.mcDeriv src dst bs ws n).stmt.flatten b : List Instr)
      = EddMemcpySAsm.eddMemcpy_prog := rfl

/-- ⭐ **`edd_memcpy` at its linked guest address.**  Entered with
    `a0` = source, `a1` = destination, `a2 = n` and an aligned return
    address, the `n`-byte destination window becomes the source prefix
    (`mcStatic` carries the bounds/no-wrap/disjointness facts). -/
theorem eddMemcpyFlat_spec (src dst ret : Word) (bs ws0 : List (BitVec 8))
    (n : Nat)
    (hro : (Region.mk src bs).wf) (hrw : (RwRegion.mk dst n).wf)
    (hw : ws0.length = n)
    (hst : EddMemcpySAsm.mcStatic src dst bs ws0 n)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (EddMemcpySAsm.mcDeriv src dst bs ws0 n).stmt.steps
      EddMcB ret eddMcCode
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ dst) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        regOwns leafScr12 ** bytesRegion src bs ** bytesRegion dst ws0)
      (((.x1 : Reg) ↦ᵣ ret) ** regOwns exposedRegs **
        bytesRegion src bs ** bytesRegion dst (bs.take n)) := by
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns leafScr12 (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x11 : Reg) ↦ᵣ dst) ** ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion src bs ** bytesRegion dst ws0)
      (fun vf => ?_))
  have hret := EddMemcpySAsm.eddMemcpy_retSpec src dst bs ws0 n EddMcB ret
    hro hrw halign
  rw [eddMc_flatten] at hret
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hret
  · refine sepConj_mono_right (fun h' hp' => ?_) h (by xperm_hyp hp :
      ((((.x1 : Reg) ↦ᵣ ret)) **
        (((((.x10 : Reg) ↦ᵣ src) ** ((.x11 : Reg) ↦ᵣ dst) **
          ((.x12 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
          regAtomsOf vf leafScr12) ** bytesRegion dst ws0) **
          bytesRegion src bs)) h)
    show (asrtOf ⟨dst, n⟩ _ ** bytesRegion src bs) h'
    refine sepConj_mono_left (fun h'' hp'' => ?_) h' hp'
    refine ⟨rf3 src dst (BitVec.ofNat 64 n) vf, ws0, empAssertion, hw,
      pcFree_emp,
      ⟨rf3_get10 _ _ _ _, rf3_get11 _ _ _ _, rf3_get12 _ _ _ _,
        rfl, hst, rfl⟩, ?_⟩
    rw [sepConj_emp_right',
      regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
      rf3_atoms]
    exact hp''
  · refine sepConj_mono_right (fun h' hq' => ?_) h hq
    have hq'' : (asrtOf ⟨dst, n⟩ _ ** bytesRegion src bs) h' := hq'
    have hq3 := sepConj_mono_left (fun h'' hq2 => by
      obtain ⟨rf, ws, A, -, -, ⟨rfl, -, rfl⟩, hh⟩ := hq2
      rw [sepConj_emp_right', regFileIs_eq_regAtoms,
        regAtoms_eq_regAtomsOf _ _ (by decide)] at hh
      exact sepConj_mono_left (regAtomsOf_to_regOwns _ _) h'' hh)
      h' hq''
    xperm_hyp hq3

#print axioms modexpIszeroFlat_spec
#print axioms spncFlat_spec
#print axioms eddBe32EqFlat_spec
#print axioms eddMemcpyFlat_spec

end EvmAsm.Codegen.DCodeLeafFlatEntries
