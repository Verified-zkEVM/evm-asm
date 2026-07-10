/-
  EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsmBody

  Shared plumbing for the `secp256k1_point_double` capstone, split out of
  `Secp256k1PointDoubleSAsm.lean` (file-size guardrail): register-ownership
  splits over the callee-scratch lists, ∃-post and `pcFree` helpers, the
  `nlz = 32 ⟺ beBytesToNat = 0` branch-condition bridge, staging-point
  wire-image lemmas (`setBytes_cover`/`arena_pair`/`curveDbl_lt`),
  owned-destination instruction steps, and the saved-register valuation
  functions.
-/

import EvmAsm.Codegen.Programs.Secp256k1PointDoubleSAsmStage

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Crypto

namespace Secp256k1PointDoubleSAsm

open EvmAsm.Rv64.SAsm.WhileBreakDemo (nlz nlz_le nlz_spec nlz_boundary)


-- ============================================================================
-- Register-ownership splits
-- ============================================================================

/-- Exposed registers other than `t0`/`a0`/`a1`. -/
def csrsScratch : List Reg :=
  [.x6, .x7, .x28, .x29, .x30, .x31, .x12, .x13, .x14, .x15, .x16, .x17]

theorem ownsSplitA0 :
    regOwns exposedRegs = (regOwns [.x10] ** regOwns a0Rest) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [a0Rest, regOwns_cons, regOwns_nil, sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

theorem ownsA0Split11 :
    regOwns a0Rest = (regOwn .x11 ** regOwns convScratch) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [convScratch, regOwns_cons, regOwns_nil]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

theorem ownsSplit1011 :
    regOwns exposedRegs = (regOwns [.x10, .x11] ** regOwns convScratch) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [convScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

theorem ownsSplit5 :
    regOwns exposedRegs = (regOwns [.x5] ** regOwns csrsRest) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [csrsRest, regOwns_cons, regOwns_nil, sepConj_emp_right']

theorem ownsCsrs1011 :
    regOwns csrsRest = (regOwns [.x10, .x11] ** regOwns csrsScratch) := by
  show regOwns
      [.x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [csrsScratch, regOwns_cons, regOwns_nil, sepConj_emp_right']
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

theorem ownsConvSplit5 :
    regOwns convScratch = (regOwn .x5 ** regOwns csrsScratch) := by
  show regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [csrsScratch, regOwns_cons, regOwns_nil]

-- ============================================================================
-- ∃-post plumbing and pcFree helpers
-- ============================================================================

/-- Pull an atom out of an ∃-post. -/
theorem exists_pull {α : Sort _} {F : α → Assertion} {G : Assertion}
    (h : PartialState) (hin : ∃ a, (G ** F a) h) :
    (G ** (fun hp => ∃ a, F a hp) : Assertion) h := by
  obtain ⟨a, h1, h2, hd, hu, hG, hFa⟩ := hin
  exact ⟨h1, h2, hd, hu, hG, ⟨a, hFa⟩⟩

/-- Pull two data out of an ∃-post. -/
theorem exists_pull2 {α β : Sort _} {F : α → β → Assertion}
    {G : Assertion} (h : PartialState) (hin : ∃ a b, (G ** F a b) h) :
    (G ** (fun hp => ∃ a b, F a b hp) : Assertion) h := by
  obtain ⟨a, b, h1, h2, hd, hu, hG, hF⟩ := hin
  exact ⟨h1, h2, hd, hu, hG, ⟨a, b, hF⟩⟩

/-- `pcFree` for a doubly-existential post. -/
theorem pcFree_exists2 {α β : Sort _} {F : α → β → Assertion}
    (h : ∀ a b, (F a b).pcFree) :
    Assertion.pcFree (fun hp => ∃ a b, F a b hp) := by
  rintro hp ⟨a, b, hF⟩
  exact h a b hp hF

/-- `pcFree` for a disjunctive post. -/
theorem pcFree_or {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    Assertion.pcFree (fun hp => P hp ∨ Q hp) := by
  rintro hp (h | h)
  · exact hP hp h
  · exact hQ hp h

-- ============================================================================
-- Branch-condition bridge: `nlz = 32` ⟺ `beBytesToNat = 0`
-- ============================================================================

theorem foldl_be' (bs : List (BitVec 8)) (acc : Nat) :
    List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) acc bs
      = acc * 256 ^ bs.length
        + List.foldl (fun a (b : BitVec 8) => a * 256 + b.toNat) 0 bs := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (acc * 256 + b.toNat), ih (0 * 256 + b.toNat)]
    have h : acc * 256 * 256 ^ bs.length = acc * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ bs.length) 256, ← Nat.mul_assoc]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    omega

/-- A big-endian buffer decodes to zero iff every byte is zero. -/
theorem beBytesToNat_eq_zero_iff (bs : List (BitVec 8)) :
    beBytesToNat bs = 0 ↔ ∀ b ∈ bs, b = 0 := by
  induction bs with
  | nil => simp [beBytesToNat]
  | cons b bs ih =>
    have hdec : beBytesToNat (b :: bs)
        = b.toNat * 256 ^ bs.length + beBytesToNat bs := by
      show List.foldl _ 0 (b :: bs) = _
      rw [List.foldl_cons, foldl_be']
      show (0 * 256 + b.toNat) * 256 ^ bs.length + beBytesToNat bs = _
      ring_nf
    have hpow : 0 < 256 ^ bs.length := Nat.pow_pos (by norm_num)
    rw [hdec]
    constructor
    · intro h
      have hmul : b.toNat * 256 ^ bs.length = 0 := by omega
      have hb : b.toNat = 0 :=
        (Nat.mul_eq_zero.mp hmul).resolve_right (by omega)
      intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hmem
      · exact BitVec.eq_of_toNat_eq (by simpa using hb)
      · exact (ih.mp (by omega)) b' hmem
    · intro h
      have hb : b.toNat = 0 := by
        have := h b (List.mem_cons_self ..)
        simp [this]
      have hbs : beBytesToNat bs = 0 :=
        ih.mpr (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      rw [hb, hbs, Nat.zero_mul, Nat.zero_add]

/-- The `secf_is_zero32` scan verdict is exactly `beBytesToNat = 0`. -/
theorem nlz32_iff_zero (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    nlz bs 32 = 32 ↔ beBytesToNat bs = 0 := by
  rw [beBytesToNat_eq_zero_iff]
  constructor
  · intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hz := nlz_spec bs 32 i (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at hz
  · intro h
    by_contra hne
    have hlt : nlz bs 32 < 32 := lt_of_le_of_ne (nlz_le bs 32) hne
    have hnz := nlz_boundary bs 32 hlt (by omega)
    have hmem : bs.getD (nlz bs 32) 0 ∈ bs := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega : nlz bs 32 < bs.length),
        Option.getD_some]
      exact List.getElem_mem _
    exact hnz (h _ hmem)

-- ============================================================================
-- Wire-image plumbing
-- ============================================================================

/-- A splice that covers the whole buffer replaces it. -/
theorem setBytes_cover (l ns : List (BitVec 8))
    (hlen : ns.length = l.length) : setBytes l 0 ns = ns := by
  apply List.ext_getElem
  · rw [length_setBytes, hlen]
  intro k hk1 hk2
  have hg := getByteAt_setBytes ns l 0 k (by omega)
  rw [if_pos ⟨by omega, by omega⟩] at hg
  have hgl : getByteAt (setBytes l 0 ns) k = (setBytes l 0 ns)[k]'hk1 := by
    unfold getByteAt
    rw [dif_pos]
  have hgr : getByteAt ns (k - 0) = ns[k]'hk2 := by
    unfold getByteAt
    rw [show k - 0 = k from by omega, dif_pos hk2]
  rw [hgl, hgr] at hg
  exact hg

/-- Both tangent-doubling components are reduced mod the (2^256-bounded)
    prime. -/
theorem curveDbl_lt (x y : Nat) :
    (Accel.curveDbl Accel.secpP x y).1 < 2 ^ 256
    ∧ (Accel.curveDbl Accel.secpP x y).2 < 2 ^ 256 := by
  have hp : 0 < Accel.secpP := by decide
  have hb : Accel.secpP < 2 ^ 256 := by decide
  unfold Accel.curveDbl
  exact ⟨lt_trans (Nat.mod_lt _ hp) hb, lt_trans (Nat.mod_lt _ hp) hb⟩

/-- The 64-byte staging point splits into its two coordinate halves. -/
theorem arena_pair (v : Nat × Nat) :
    bytesRegion arenaB (pairBytes 4 v)
      = (bytesRegion (0xa3c05618 : Word) (leBytes32 v.1)
        ** bytesRegion (0xa3c05638 : Word) (leBytes32 v.2)) := by
  show bytesRegion arenaB (leBytes32 v.1 ++ leBytes32 v.2) = _
  rw [bytesRegion_append _ _ _ ⟨4, by rw [length_leBytes32]⟩, length_leBytes32,
    show arenaB + BitVec.ofNat 64 32 = (0xa3c05638 : Word) from by decide,
    show arenaB = (0xa3c05618 : Word) from by decide]

-- ============================================================================
-- Owned-destination instruction steps (the incumbent value is immaterial)
-- ============================================================================

/-- `la` into an owned register. -/
theorem la_own_within (rd : Reg) {pc target : Word}
    (h : ∀ vOld, cpsTripleWithin 2 pc (pc + 8) pdCr
      (rd ↦ᵣ vOld) (rd ↦ᵣ target)) :
    cpsTripleWithin 2 pc (pc + 8) pdCr (regOwn rd) (rd ↦ᵣ target) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn_single h

/-- `mv` into an owned register. -/
theorem mv_own_within (rd rs : Reg) (v : Word) (addr : Word)
    (hrd : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.MV rd rs))
      ((rs ↦ᵣ v) ** regOwn rd) ((rs ↦ᵣ v) ** (rd ↦ᵣ v)) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn (fun vOld =>
    mv_spec_gen_within rd rs v vOld addr hrd)

/-- `addi` into an owned register. -/
theorem addi_own_within (rd rs1 : Reg) (v1 : Word) (imm : BitVec 12)
    (addr : Word) (hrd : rd ≠ .x0) :
    cpsTripleWithin 1 addr (addr + 4) (CodeReq.singleton addr (.ADDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** regOwn rd)
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  cpsTripleWithin_of_forall_regIs_to_regOwn (fun vOld =>
    addi_spec_gen_within rd rs1 vOld v1 imm addr hrd)

-- ============================================================================
-- Entry / per-path exit values of the saved registers
-- ============================================================================

/-- Entry values of the saved registers. -/
def pdVals (ret v8 v9 : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => ret | .x8 => v8 | .x9 => v9 | _ => 0

/-- Body-exit values on the infinity path: `ra` = the second `secf_zero32`
    link, `s0`/`s1` the pointer copies. -/
def pdValsInf (inPtr outPtr : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => (0x800205ac : Word) | .x8 => inPtr | .x9 => outPtr | _ => 0

/-- Body-exit values on the accelerator path: `ra` = the last
    `secf_le_to_be` link. -/
def pdValsReg (inPtr outPtr : Word) : Reg → Word :=
  fun r => match r with
  | .x1 => (0x80020608 : Word) | .x8 => inPtr | .x9 => outPtr | _ => 0

end Secp256k1PointDoubleSAsm

end EvmAsm.Codegen
