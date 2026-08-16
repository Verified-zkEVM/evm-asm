import EvmAsm.Rv64.RLP.RecDecode.Widen
import EvmAsm.Rv64.BitAux
import EvmAsm.Rv64.RLP.RecDecode.VcgenK
namespace EvmAsm.Rv64.SAsm.RecDecode
open Stmt
open EvmAsm.EL.RLP (Byte)

/-- Dev copy of the items post (merged into Body.lean at the end). -/
def itemsPostV' (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) : Reach :=
  fun rf ws A =>
    rf.get .x10 = itemsStatus bs pStart (pEnd - pStart) d
    ∧ rf.get .x13 = fp
    ∧ ws.take 8 = dwordBytes v
    ∧ A = A₀

/-- Dev copy of the items Fn (merged into Body.lean at the end). -/
def itemsFnV' (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (beS childS : FnHandleS) : Fn where
  name := "rlpitems"
  region := ⟨inBase, bs⟩
  rw := itemsRw d fp
  pre := Reach.exact rf₀ (setBytes ws₀ 0 (dwordBytes v)) A₀
  post := itemsPostV' bs inBase d fp pStart pEnd v A₀
  body := itemsBody bs.length (decInv bs inBase d fp pStart pEnd v A₀)
    beS childS

private theorem itemsPin_flat :
    itemsFnPin.body.offsetsOk = true ∧ 4 * itemsFnPin.body.size < 2 ^ 64 := by
  constructor
  · decide +kernel
  · decide +kernel

private theorem items_offsetsOk_eq (N : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS) :
    (itemsBody N inv beS childS).offsetsOk = itemsFnPin.body.offsetsOk := rfl

private theorem items_size_eq (N : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS) :
    (itemsBody N inv beS childS).size = itemsFnPin.body.size := rfl

private theorem items_flatten_eq (N : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS) :
    (itemsBody N inv beS childS).flatten (itemsEntry + 4)
      = itemsFnPin.body.flatten (itemsEntry + 4) := rfl

private theorem itemsFlat_len :
    (itemsFnPin.body.flatten (itemsEntry + 4)).length = 90 := rfl

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by
  decide
private theorem se12_24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by
  decide
private theorem se12_32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by
  decide
private theorem se12_n32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  decide
private theorem se12_n1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  decide
private theorem se12_n7F : signExtend12 (-0x7F : BitVec 12)
    = (-0x7F : Word) := by decide
private theorem se12_nB7 : signExtend12 (-0xB7 : BitVec 12)
    = (-0xB7 : Word) := by decide
private theorem se12_nBF : signExtend12 (-0xBF : BitVec 12)
    = (-0xBF : Word) := by decide
private theorem se12_nF7 : signExtend12 (-0xF7 : BitVec 12)
    = (-0xF7 : Word) := by decide

/-- The loop guard in offset terms: with both cursors inside a non-wrapping
    region window, `bltu` is the offset order. -/
private theorem guard_iff (inBase : Word) (c q : Nat) (rf : RegFile)
    (h15 : rf.get .x15 = inBase + BitVec.ofNat 64 c)
    (h16 : rf.get .x16 = inBase + BitVec.ofNat 64 q)
    (hbound : inBase.toNat + q < 2 ^ 64) (hcq : c ≤ q) :
    (Cond.bltu .x15 .x16).holds rf ↔ c < q := by
  show BitVec.ult (rf.get .x15) (rf.get .x16) = true ↔ c < q
  rw [h15, h16]
  constructor
  · intro h
    by_contra hge
    have hceq : c = q := by omega
    subst hceq
    simp [BitVec.ult] at h
  · intro h
    have h1 : (inBase + BitVec.ofNat 64 c).toNat = inBase.toNat + c := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have h2 : (inBase + BitVec.ofNat 64 q).toNat = inBase.toNat + q := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    simp only [BitVec.ult, decide_eq_true_eq, h1, h2]
    omega

/-- Low-bit masking is the identity on even words (dev copy). -/
private theorem and_not_one_of_even' (x : Word) (h : 2 ∣ x.toNat) :
    x &&& ~~~(1 : Word) = x := by
  apply BitAux.word_andn_one_of_even
  apply BitVec.eq_of_toNat_eq
  show x.toNat &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

set_option maxRecDepth 8000 in
theorem itemsFnV'_spec (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (beS childS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hpq : pStart ≤ pEnd)
    (hq : pEnd ≤ bs.length)
    (hx15 : rf₀.get .x15 = inBase + BitVec.ofNat 64 pStart)
    (hx16 : rf₀.get .x16 = inBase + BitVec.ofNat 64 pEnd)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (hws₀ : ws₀.length = 40 * d + 40)
    (hd64 : d < 2 ^ 64)
    (hbeE : beS.entry = rdbeEntry)
    (hbeCode : ∀ a i, beS.code a = some i → decCr a = some i)
    (hbeReg : beS.region = (⟨inBase, bs⟩ : Region))
    (hbeRw : beS.rw = itemsRw d fp)
    (hbePre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
        (j n : Nat), rf.get .x29 = inBase + BitVec.ofNat 64 j →
        rf.get .x30 = BitVec.ofNat 64 n → n ≤ 8 → j + n ≤ bs.length →
        beS.pre rf ws A)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (hcE : childS.entry = decEntry)
    (hcCode : ∀ a i, childS.code a = some i → decCr a = some i)
    (hcReg : childS.region = (⟨inBase, bs⟩ : Region))
    (hcRw : childS.rw = itemsRw d fp)
    (hcPre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        decPreS bs inBase d (fp + 32) rf ws A → childS.pre rf ws A)
    (hcPost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        childS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = decStatus bs (offOf inBase rf₁) (lenOf rf₁) d
          ∧ rf.get .x13 = fp + 32
          ∧ ws.take 32 = ws₁.take 32
          ∧ A = A₁) :
    (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS).SpecR
      (itemsEntry + 4) decCr := by
  show Fn.SpecR _ _ _
  vcgenK
  case region => exact ⟨L.regWf, L.rwWf⟩
  case rlpitems.flat =>
    refine ⟨?_, ?_⟩
    · rw [show (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS
          childS).body.offsetsOk = itemsFnPin.body.offsetsOk from
        items_offsetsOk_eq bs.length _ beS childS]
      exact itemsPin_flat.1
    · rw [show (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS
          childS).body.size = itemsFnPin.body.size from
        items_size_eq bs.length _ beS childS]
      exact itemsPin_flat.2
  case code =>
    intro a i h
    have h' : CodeReq.ofProg (itemsEntry + 4)
        (itemsFnPin.body.flatten (itemsEntry + 4)) a = some i := by
      rw [show (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS
          childS).body.flatten (itemsEntry + 4)
        = itemsFnPin.body.flatten (itemsEntry + 4) from
          items_flatten_eq bs.length _ beS childS] at h
      exact h
    have h2 : CodeReq.ofProg itemsEntry itemsProg a = some i := by
      show CodeReq.ofProg itemsEntry (.SD .x13 .x1 0 ::
          (itemsFnPin.body.flatten (itemsEntry + 4)
            ++ [.LD .x1 .x13 0, .JALR .x0 .x1 0])) a = some i
      refine ofProg_cons_tail ?_ a i (ofProg_mono_left a i h')
      rw [List.length_append, itemsFlat_len]
      decide
    -- decCr = (dec ∪ items) ∪ rdbe: route through the middle element
    have hdecNone : CodeReq.ofProg decEntry decProg a = none := by
      obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h2
      have hk' : kk < itemsProg.length := hk
      have hkk : kk < 93 := by
        rw [show itemsProg.length = 93 from rfl] at hk'
        exact hk'
      apply CodeReq.ofProg_none_range
      intro k' hk2 heq
      have hk2' : k' < decProg.length := hk2
      have hkk2 : k' < 106 := by
        rw [show decProg.length = 106 from rfl] at hk2'
        exact hk2'
      have heq' : (0x1400 : Word) + BitVec.ofNat 64 (4 * kk)
          = (0x1000 : Word) + BitVec.ofNat 64 (4 * k') := heq
      exact absurd heq' (by bv_omega)
    simp only [decCr, CodeReq.union, hdecNone, h2]
  case callees =>
    and_intros
    all_goals first
      | trivial
      | (intro h hmem
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
         subst hmem
         first
           | exact ⟨hbeCode, hbeReg, hbeRw⟩
           | exact ⟨hcCode, hcReg, hcRw⟩)
  case calls =>
    and_intros
    all_goals first
      | (apply and_not_one_of_even'
         have h1 : itemsEntry.toNat = 0x1400 := rfl
         have h4 : ((4 : Word)).toNat = 4 := rfl
         simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1, h4]
         omega)
      | (intro h hmem
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
         subst hmem
         first
           | (rw [hbeE]; decide)
           | (rw [hcE]; decide))
      | trivial
  case rlpitems.iloop.inv_init =>
    rintro rf ws A ⟨rfE, wsE, hlenE, ⟨h1, h2, h3⟩, hrf, hws⟩
    subst hrf
    have hws' : ws = wsE := hws
    refine ⟨pStart, le_refl _, hpq, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), h1, hx15]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), h1, hx16]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), h1, hx12]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide), h1, hx13]
    · rw [hws', h2]
      have hs := setBytes_slot ws₀ (dwordBytes v) 0
        (by rw [length_dwordBytes]; omega)
      rw [List.drop_zero, length_dwordBytes] at hs
      exact hs
    · rw [hws', h2, length_setBytes, hws₀]
    · exact h3
    · left
      refine ⟨?_, Iff.rfl⟩
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
  case rlpitems.iloop.exhausted =>
    rintro rf ws A ⟨c, hc1, hc2, hci, h15, h16, -, -, -, -, -, -⟩ hcond
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hlt := (guard_iff inBase c pEnd rf h15 h16 (by omega) hc2).mp hcond
    omega
  all_goals try decide
  run_tac do
    for g in ← Lean.Elab.Tactic.getUnsolvedGoals do
      Lean.logInfo m!"REMAIN {← g.getTag}"
  all_goals sorry

end EvmAsm.Rv64.SAsm.RecDecode
