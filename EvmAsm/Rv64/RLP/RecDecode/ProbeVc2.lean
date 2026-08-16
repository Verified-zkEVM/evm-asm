import EvmAsm.Rv64.RLP.RecDecode.Widen
import EvmAsm.Rv64.RLP.RecDecode.ItemsStep
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

private theorem itemsFnV'_region_eq (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8)) (A₀ : Assertion) (beS childS : FnHandleS) :
    (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS).region =
      (⟨inBase, bs⟩ : Region) := by
  rfl

private theorem itemsFnV'_rw_eq (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8)) (A₀ : Assertion) (beS childS : FnHandleS) :
    (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS).rw =
      itemsRw d fp := by
  rfl

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

/-- An `LBU` whose address resolves outside the writable window reads the
    read-only region (dev copy of the demo lemma). -/
private theorem execInstrRF_lbu_ro2 (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd
          ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- Low-bit masking is the identity on even words (dev copy). -/
private theorem and_not_one_of_even' (x : Word) (h : 2 ∣ x.toNat) :
    x &&& ~~~(1 : Word) = x := by
  apply BitAux.word_andn_one_of_even
  apply BitVec.eq_of_toNat_eq
  show x.toNat &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

-- Register summary at the cascade exit, for the call-tail VCs: the frame
-- pointer is untouched; on the un-poisoned side the cursor pair, budget
-- and frame pointer are the invariant's.
set_option maxRecDepth 8000 in
private theorem cascade_regs (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (beS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁) :
    ∀ rf ws A, Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp) (itemLenCascade beS)
        (fun rf ws A => (∃ i, i < bs.length
            ∧ decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
            ∧ (Cond.bltu .x15 .x16).holds rf)) rf ws A
      → rf.get .x14 = 0 →
          rf.get .x13 = fp
          ∧ ∃ c : Nat, pStart ≤ c ∧ c < pEnd
            ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
            ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
            ∧ rf.get .x12 = BitVec.ofNat 64 d := by
  intro rf ws A hsp h14
  have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  -- one helper: everything we need from an ib0-exit state
  have hR1facts : ∀ rf1 ws1 A1, Stmt.sp ⟨inBase, bs⟩ (itemsRw d fp)
      (.block "ib0" [.LBU .x5 .x15 0, .SUB .x6 .x16 .x15, .LI .x7 0x80])
      (fun rf ws A => (∃ i, i < bs.length
          ∧ decInv bs inBase d fp pStart pEnd v A₀ i rf ws A
          ∧ (Cond.bltu .x15 .x16).holds rf)) rf1 ws1 A1 →
      ∃ c : Nat, pStart ≤ c ∧ c < pEnd
        ∧ rf1.get .x15 = inBase + BitVec.ofNat 64 c
        ∧ rf1.get .x16 = inBase + BitVec.ofNat 64 pEnd
        ∧ rf1.get .x12 = BitVec.ofNat 64 d
        ∧ rf1.get .x13 = fp
        ∧ rf1.get .x14 = 0 := by
    rintro rf1 ws1 A1 ⟨rfI, wsI, hlI, ⟨i, hif, ⟨c, hc1, hc2, hci, h15, h16,
      h12, h13, htake, hlen', hA, hst⟩, hguard⟩, hrf1, hws1⟩
    have hclt : c < pEnd := (guard_iff inBase c pEnd rfI h15 h16 (by omega)
      hc2).mp hguard
    have h14I : rfI.get .x14 = 0 := by
      rcases hst with ⟨h14, -⟩ | ⟨-, -, hce⟩
      · exact h14
      · omega
    have haddr0 : rfI.get .x15 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 c := by
      rw [se12_0, h15]
      bv_omega
    have hnorwI : ¬ inRw fp wsI
        (rfI.get .x15 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr0]
      exact L.not_inRw hlI (by omega)
    subst hrf1
    refine ⟨c, hc1, hclt, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, loadSem]
      rw [if_neg hnorwI, RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      assumption
  -- Each leaf below reduces to projections over explicit set-chains.
  rcases hsp with hL | hsp2
  · -- iL1
    obtain ⟨rf1, ws1, hl1, ⟨hR1x, -⟩, hrf, -⟩ := hL
    obtain ⟨c, hc1, hclt, e15, e16, e12, e13, -⟩ := hR1facts _ _ _ hR1x
    subst hrf
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem]
    refine ⟨?_, c, hc1, hclt, ?_, ?_, ?_⟩
    all_goals
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      assumption
  rcases hsp2 with hL | hsp2
  · -- iL2 (via ic1)
    obtain ⟨rf2, ws2, hl2, ⟨hSp, -⟩, hrf, -⟩ := hL
    obtain ⟨rf1, ws1, hl1, ⟨hR1x, -⟩, hrf2, -⟩ := hSp
    obtain ⟨c, hc1, hclt, e15, e16, e12, e13, -⟩ := hR1facts _ _ _ hR1x
    rw [hrf2] at hrf
    subst hrf
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem]
    refine ⟨?_, c, hc1, hclt, ?_, ?_, ?_⟩
    all_goals
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      assumption
  rcases hsp2 with hL | hsp2
  · -- itemLongFormB = ibll ;;; ite ibtr (ibb1 ;;; ite ibz ...) ibpt
    rcases hL with hT | hPT
    · -- ibtr taken: ibb1 ;;; ite ibz (ibpz) (...)
      rcases hT with hPZ | hE
      · -- ibpz: poison — contradicts x14 = 0
        obtain ⟨rfP, wsP, hlP, -, hrf, -⟩ := hPZ
        exfalso
        revert h14
        subst hrf
        simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
          execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
          ne_eq, reduceCtorEq, not_false_eq_true]
        decide
      · -- ibz not taken: ibargs ;;; leaf call ;;; ibrem ;;; ite ibfit
        rcases hE with hPF | hOK
        · -- ibpf: poison
          obtain ⟨rfP, wsP, hlP, -, hrf, -⟩ := hPF
          exfalso
          revert h14
          subst hrf
          simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
            execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
            ne_eq, reduceCtorEq, not_false_eq_true]
          decide
        · -- ibL: the success leaf through the length-field read
          obtain ⟨rfL2, wsL2, hlL2, ⟨hRem, -⟩, hrf, -⟩ := hOK
          obtain ⟨rfR, wsR, hlR, hCall, hrfL2, -⟩ := hRem
          obtain ⟨rf₁, ws₁, A₁, hPrior, h, hmem, hent, hpre₁, hpost₁⟩ := hCall
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          subst hmem
          obtain ⟨-, hpin, -, -⟩ := hbePost _ _ _ _ _ _ hpost₁
          obtain ⟨rfAg, wsAg, hlAg, ⟨hB1sp, -⟩, hrf₁, -⟩ := hPrior
          obtain ⟨rfB, wsB, hlB, ⟨hIbll, -⟩, hrfAg, -⟩ := hB1sp
          obtain ⟨rfC, wsC, hlC, ⟨hR1x, -⟩, hrfB, -⟩ := hIbll
          obtain ⟨rf1a, ws1a, hl1a, ⟨hSp1, -⟩, hrfC0, -⟩ := hR1x
          obtain ⟨rf0a, ws0a, hl0a, ⟨hR1y, -⟩, hrf1a, -⟩ := hSp1
          obtain ⟨c, hc1, hclt, e15, e16, e12, e13, -⟩ :=
            hR1facts _ _ _ hR1y
          -- thread through ic1, ic2, ibll (ALU on x7)
          rw [hrf1a] at hrfC0
          rw [hrfC0] at hrfB
          simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
            execInstrRF, aluSem] at hrfB
          -- through ibb1 (LBU x31): generic untouched-projection
          have thread1 : ∀ r : Reg, r ≠ .x31 → rfAg.get r = rfB.get r := by
            intro r hr
            rw [hrfAg]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil]
            exact execInstrRF_get_ne _ _ _ _ _ _ (fun op hop => nomatch hop)
              (fun l hl => by cases hl; exact hr)
          -- through ibargs (x29, x30, x28)
          have thread2 : ∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 →
              rf₁.get r = rfAg.get r := by
            intro r h1 h2 h3
            rw [hrf₁]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem]
            rw [RegFile.get_set_ne _ _ _ _ h1,
              RegFile.get_set_ne _ _ _ _ h3, RegFile.get_set_ne _ _ _ _ h2]
          -- through the leaf call (pin), ibrem (x6), ibL (x17)
          have thread3 : ∀ r : Reg, r ≠ .x6 → r ≠ .x17 → r ≠ .x28 →
              r ≠ .x29 → r ≠ .x30 → r ≠ .x31 → rf.get r = rf₁.get r := by
            intro r k6 k17 k28 k29 k30 k31
            rw [hrf]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem]
            rw [RegFile.get_set_ne _ _ _ _ k17,
              RegFile.get_set_ne _ _ _ _ k17, hrfL2]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem]
            rw [RegFile.get_set_ne _ _ _ _ k6, RegFile.get_set_ne _ _ _ _ k6]
            exact hpin r k28 k29 k30 k31
          have finalC : ∀ r : Reg, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x17 →
              r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf0a.get r := by
            intro r k5 k6 k7 k17 k28 k29 k30 k31
            rw [thread3 r k6 k17 k28 k29 k30 k31, thread2 r k28 k29 k30,
              thread1 r k31, hrfB]
            rw [RegFile.get_set_ne _ _ _ _ k7,
              RegFile.get_set_ne _ _ _ _ k7,
              RegFile.get_set_ne _ _ _ _ k7]
          refine ⟨?_, c, hc1, hclt, ?_, ?_, ?_⟩
          · rw [finalC .x13 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e13
          · rw [finalC .x15 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e15
          · rw [finalC .x16 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e16
          · rw [finalC .x12 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e12
    · -- ibpt: poison
      obtain ⟨rfP, wsP, hlP, -, hrf, -⟩ := hPT
      exfalso
      revert h14
      subst hrf
      simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
        ne_eq, reduceCtorEq, not_false_eq_true]
      decide
  rcases hsp2 with hL | hLongL
  · -- iL4 (via ic1, ic2, ic3)
    obtain ⟨rf4, ws4, hl4, ⟨hSp3, -⟩, hrf, -⟩ := hL
    obtain ⟨rf3, ws3, hl3, ⟨hSp2, -⟩, hrf4, -⟩ := hSp3
    obtain ⟨rf2, ws2, hl2, ⟨hSp1, -⟩, hrf3, -⟩ := hSp2
    obtain ⟨rf1, ws1, hl1, ⟨hR1x, -⟩, hrf2, -⟩ := hSp1
    obtain ⟨c, hc1, hclt, e15, e16, e12, e13, -⟩ := hR1facts _ _ _ hR1x
    rw [hrf2] at hrf3
    rw [hrf3] at hrf4
    rw [hrf4] at hrf
    subst hrf
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem]
    refine ⟨?_, c, hc1, hclt, ?_, ?_, ?_⟩
    all_goals
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide)]
      assumption
  · -- itemLongFormL = illl ;;; ite iltr (ilb1 ;;; ite ilz ...) ilpt
    rcases hLongL with hT | hPT
    · rcases hT with hPZ | hE
      · -- ilpz: poison
        obtain ⟨rfP, wsP, hlP, -, hrf, -⟩ := hPZ
        exfalso
        revert h14
        subst hrf
        simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
          execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
          ne_eq, reduceCtorEq, not_false_eq_true]
        decide
      · rcases hE with hPF | hOK
        · -- ilpf: poison
          obtain ⟨rfP, wsP, hlP, -, hrf, -⟩ := hPF
          exfalso
          revert h14
          subst hrf
          simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
            execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
            ne_eq, reduceCtorEq, not_false_eq_true]
          decide
        · -- ilL: the success leaf
          obtain ⟨rfL2, wsL2, hlL2, ⟨hRem, -⟩, hrf, -⟩ := hOK
          obtain ⟨rfR, wsR, hlR, hCall, hrfL2, -⟩ := hRem
          obtain ⟨rf₁, ws₁, A₁, hPrior, h, hmem, hent, hpre₁, hpost₁⟩ := hCall
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          subst hmem
          obtain ⟨-, hpin, -, -⟩ := hbePost _ _ _ _ _ _ hpost₁
          obtain ⟨rfAg, wsAg, hlAg, ⟨hB1sp, -⟩, hrf₁, -⟩ := hPrior
          obtain ⟨rfB, wsB, hlB, ⟨hIbll, -⟩, hrfAg, -⟩ := hB1sp
          obtain ⟨rfC, wsC, hlC, ⟨hR4x, -⟩, hrfB, -⟩ := hIbll
          obtain ⟨rf2a, ws2a, hl2a, ⟨hR3x, -⟩, hrfC0, -⟩ := hR4x
          obtain ⟨rf1a, ws1a, hl1a, ⟨hSp1x, -⟩, hrf2a, -⟩ := hR3x
          obtain ⟨rf0a, ws0a, hl0a, ⟨hR1y, -⟩, hrf1a, -⟩ := hSp1x
          obtain ⟨c, hc1, hclt, e15, e16, e12, e13, -⟩ :=
            hR1facts _ _ _ hR1y
          rw [hrf1a] at hrf2a
          rw [hrf2a] at hrfC0
          rw [hrfC0] at hrfB
          simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
            execInstrRF, aluSem] at hrfB
          have thread1 : ∀ r : Reg, r ≠ .x31 → rfAg.get r = rfB.get r := by
            intro r hr
            rw [hrfAg]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil]
            exact execInstrRF_get_ne _ _ _ _ _ _ (fun op hop => nomatch hop)
              (fun l hl => by cases hl; exact hr)
          have thread2 : ∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 →
              rf₁.get r = rfAg.get r := by
            intro r h1 h2 h3
            rw [hrf₁]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem]
            rw [RegFile.get_set_ne _ _ _ _ h1,
              RegFile.get_set_ne _ _ _ _ h3, RegFile.get_set_ne _ _ _ _ h2]
          have thread3 : ∀ r : Reg, r ≠ .x6 → r ≠ .x17 → r ≠ .x28 →
              r ≠ .x29 → r ≠ .x30 → r ≠ .x31 → rf.get r = rf₁.get r := by
            intro r k6 k17 k28 k29 k30 k31
            rw [hrf]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem]
            rw [RegFile.get_set_ne _ _ _ _ k17,
              RegFile.get_set_ne _ _ _ _ k17, hrfL2]
            simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem]
            rw [RegFile.get_set_ne _ _ _ _ k6, RegFile.get_set_ne _ _ _ _ k6]
            exact hpin r k28 k29 k30 k31
          have finalC : ∀ r : Reg, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x17 →
              r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf0a.get r := by
            intro r k5 k6 k7 k17 k28 k29 k30 k31
            rw [thread3 r k6 k17 k28 k29 k30 k31, thread2 r k28 k29 k30,
              thread1 r k31, hrfB]
            rw [RegFile.get_set_ne _ _ _ _ k7,
              RegFile.get_set_ne _ _ _ _ k7,
              RegFile.get_set_ne _ _ _ _ k7,
              RegFile.get_set_ne _ _ _ _ k7]
          refine ⟨?_, c, hc1, hclt, ?_, ?_, ?_⟩
          · rw [finalC .x13 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e13
          · rw [finalC .x15 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e15
          · rw [finalC .x16 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e16
          · rw [finalC .x12 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)]
            exact e12
    · -- ilpt: poison
      obtain ⟨rfP, wsP, hlP, -, hrf, -⟩ := hPT
      exfalso
      revert h14
      subst hrf
      simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
        execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
        ne_eq, reduceCtorEq, not_false_eq_true]
      decide

-- The spill block's store conditions, in a fresh declaration budget.
set_option maxRecDepth 8000 in
private theorem spill_mem_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (ws : List (BitVec 8))
    (hfw : fp.toNat + (40 * d + 40) < 2 ^ 64)
    (hws : ws.length = 40 * d + 40)
    (e13 : rfF.get .x13 = fp)
    (hrfS : rf = (execBlock ⟨inBase, bs⟩ fp rfF wsF
        [.SUB .x6 .x16 .x15]).1) :
    blockVCs ⟨inBase, bs⟩ fp rf ws
       [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)] := by
  have h13 : rf.get .x13 = fp := by
    rw [hrfS]
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
      ne_eq, reduceCtorEq, not_false_eq_true]
    exact e13
  have h8 : (rf.get .x13 + signExtend12 (8 : BitVec 12) - fp).toNat = 8 := by
    rw [h13, se12_8]
    bv_omega
  have h16 : (rf.get .x13 + signExtend12 (16 : BitVec 12) - fp).toNat = 16 := by
    rw [h13, se12_16]
    bv_omega
  have h24 : (rf.get .x13 + signExtend12 (24 : BitVec 12) - fp).toNat = 24 := by
    rw [h13, se12_24]
    bv_omega
  have h8' : ((rf.set .x7 (rf.get .x15 + rf.get .x17)).get .x13
      + signExtend12 (8 : BitVec 12) - fp).toNat = 8 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]
    exact h8
  have h16' : ((rf.set .x7 (rf.get .x15 + rf.get .x17)).get .x13
      + signExtend12 (16 : BitVec 12) - fp).toNat = 16 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]
    exact h16
  have h24' : ((rf.set .x7 (rf.get .x15 + rf.get .x17)).get .x13
      + signExtend12 (24 : BitVec 12) - fp).toNat = 24 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]
    exact h24
  simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, inRw,
    length_setBytes, h8', h16', h24', hws]
  and_intros
  all_goals norm_num
  all_goals omega

-- The reload block's load conditions, in a fresh declaration budget.
set_option maxRecDepth 8000 in
private theorem reload_mem_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (rf : RegFile) (ws : List (BitVec 8))
    (hfw : fp.toNat + (40 * d + 40) < 2 ^ 64)
    (hws : ws.length = 40 * d + 40)
    (h13P : rf.get .x13 = fp + 32) :
    blockVCs ⟨inBase, bs⟩ fp rf ws
       [.ADDI .x13 .x13 (-32), .LD .x15 .x13 8, .LD .x16 .x13 16,
       .LD .x12 .x13 24] := by
  have h13 : (rf.set .x13 fp).get .x13 = fp :=
    RegFile.get_set_self _ _ _ (by decide)
  have h13' : rf.get .x13 + signExtend12 (-32 : BitVec 12) = fp := by
    rw [h13P, se12_n32]
    bv_omega
  have h8 : ((rf.set .x13 fp).get .x13 + signExtend12 (8 : BitVec 12)
      - fp).toNat = 8 := by
    rw [h13, se12_8]
    bv_omega
  have h16 : ((rf.set .x13 fp).get .x13 + signExtend12 (16 : BitVec 12)
      - fp).toNat = 16 := by
    rw [h13, se12_16]
    bv_omega
  have h24 : ((rf.set .x13 fp).get .x13 + signExtend12 (24 : BitVec 12)
      - fp).toNat = 24 := by
    rw [h13, se12_24]
    bv_omega
  have hstep : execInstrRF ⟨inBase, bs⟩ fp rf ws
      (.ADDI .x13 .x13 (-32)) = (rf.set .x13 fp, ws) := by
    simp only [execInstrRF, aluSem, h13']
  have h8r : inRw fp ws (fp + signExtend12 (8 : BitVec 12)) 8 := by
    unfold inRw
    rw [show (fp + signExtend12 (8 : BitVec 12) - fp).toNat = 8 by
      rw [se12_8]; bv_omega, hws]
    omega
  have h16r : inRw fp ws (fp + signExtend12 (16 : BitVec 12)) 8 := by
    unfold inRw
    rw [show (fp + signExtend12 (16 : BitVec 12) - fp).toNat = 16 by
      rw [se12_16]; bv_omega, hws]
    omega
  have h24r : inRw fp ws (fp + signExtend12 (24 : BitVec 12)) 8 := by
    unfold inRw
    rw [show (fp + signExtend12 (24 : BitVec 12) - fp).toNat = 24 by
      rw [se12_24]; bv_omega, hws]
    omega
  have h8r' : inRw fp ws
      ((rf.set .x13 fp).get .x13 + signExtend12 (8 : BitVec 12)) 8 := by
    rw [h13]
    exact h8r
  have h8ok : (Region.mk fp ws).loadOk
      (fp + signExtend12 (8 : BitVec 12)) 8 := by
    unfold Region.loadOk
    rw [show (fp + signExtend12 (8 : BitVec 12) - fp).toNat = 8 by
      rw [se12_8]; bv_omega, hws]
    constructor <;> norm_num
  have h16ok : (Region.mk fp ws).loadOk
      (fp + signExtend12 (16 : BitVec 12)) 8 := by
    unfold Region.loadOk
    rw [show (fp + signExtend12 (16 : BitVec 12) - fp).toNat = 16 by
      rw [se12_16]; bv_omega, hws]
    constructor <;> norm_num
  have h24ok : (Region.mk fp ws).loadOk
      (fp + signExtend12 (24 : BitVec 12)) 8 := by
    unfold Region.loadOk
    rw [show (fp + signExtend12 (24 : BitVec 12) - fp).toNat = 24 by
      rw [se12_24]; bv_omega, hws]
    constructor <;> norm_num
  have hload1x13 :
      (execInstrRF ⟨inBase, bs⟩ fp (rf.set .x13 fp) ws
        (.LD .x15 .x13 8)).1.get .x13 = fp := by
    simp only [execInstrRF, aluSem, loadSem]
    rw [if_pos h8r']
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hload1ws :
      (execInstrRF ⟨inBase, bs⟩ fp (rf.set .x13 fp) ws
        (.LD .x15 .x13 8)).2 = ws := by
    simp only [execInstrRF, aluSem, loadSem]
  have hload1rf :
      (execInstrRF ⟨inBase, bs⟩ fp (rf.set .x13 fp) ws
        (.LD .x15 .x13 8)).1 =
        (rf.set .x13 fp).set .x15
          ((Region.mk fp ws).dwordAt
            ((rf.set .x13 fp).get .x13 + signExtend12 (8 : BitVec 12))) := by
    simp only [execInstrRF, aluSem, loadSem]
    rw [if_pos h8r']
  have hload2rf :
      (execInstrRF ⟨inBase, bs⟩ fp
        ((rf.set .x13 fp).set .x15
          ((Region.mk fp ws).dwordAt
            (fp + signExtend12 (8 : BitVec 12)))) ws
        (.LD .x16 .x13 16)).1 =
        ((rf.set .x13 fp).set .x15
          ((Region.mk fp ws).dwordAt
            (fp + signExtend12 (8 : BitVec 12)))).set .x16
          ((Region.mk fp ws).dwordAt
            (fp + signExtend12 (16 : BitVec 12))) := by
    simp only [execInstrRF, aluSem, loadSem, h13, RegFile.get_set_ne,
      RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [if_pos h16r]
  have hload2ws :
      (execInstrRF ⟨inBase, bs⟩ fp
        ((rf.set .x13 fp).set .x15
          ((Region.mk fp ws).dwordAt
            (fp + signExtend12 (8 : BitVec 12)))) ws
        (.LD .x16 .x13 16)).2 = ws := by
    simp only [execInstrRF, aluSem, loadSem]
  simp only [blockVCs, loadSem, storeSem, aluSem]
  rw [hstep]
  simp only [Prod.fst, Prod.snd]
  refine ⟨trivial, ?_⟩
  rw [h13]
  rw [if_pos h8r]
  refine ⟨h8ok, ?_⟩
  rw [hload1rf, hload1ws]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true]
  rw [if_pos h16r]
  refine ⟨h16ok, ?_⟩
  rw [hload2rf]
  rw [hload2ws]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true]
  rw [if_pos h24r]
  exact ⟨h24ok, trivial⟩

set_option maxRecDepth 8000 in
private theorem spill_regs_core (ro : Region) (rwBase fp : Word)
    (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (h13 : rfF.get .x13 = fp)
    (hrf : rf = (execBlock ro rwBase rfF wsF
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]).1) :
      rf.get .x10 = rfF.get .x15 ∧ rf.get .x11 = rfF.get .x17
      ∧ rf.get .x12 = rfF.get .x12 ∧ rf.get .x13 = rfF.get .x13 + 32
      ∧ rf.get .x28 = decEntry := by
  have h8 : (rfF.get .x13 + signExtend12 (8 : BitVec 12) - fp).toNat = 8 := by
    rw [h13, se12_8]
    bv_omega
  have h16 : (rfF.get .x13 + signExtend12 (16 : BitVec 12) - fp).toNat = 16 := by
    rw [h13, se12_16]
    bv_omega
  have h24 : (rfF.get .x13 + signExtend12 (24 : BitVec 12) - fp).toNat = 24 := by
    rw [h13, se12_24]
    bv_omega
  have h8' : ((rfF.set .x7 (rfF.get .x15 + rfF.get .x17)).get .x13
      + signExtend12 (8 : BitVec 12) - fp).toNat = 8 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]
    exact h8
  have h16' : ((rfF.set .x7 (rfF.get .x15 + rfF.get .x17)).get .x13
      + signExtend12 (16 : BitVec 12) - fp).toNat = 16 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]
    exact h16
  have h24' : ((rfF.set .x7 (rfF.get .x15 + rfF.get .x17)).get .x13
      + signExtend12 (24 : BitVec 12) - fp).toNat = 24 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7)]
    exact h24
  have h32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
    storeSem, h32, RegFile.get_set_ne, RegFile.get_set_self,
    ne_eq, reduceCtorEq, not_false_eq_true]
  simpa [decEntry]

private theorem spill_x10 (ro : Region) (rwBase fp : Word)
    (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (h13 : rfF.get .x13 = fp)
    (hrf : rf = (execBlock ro rwBase rfF wsF
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]).1) :
    rf.get .x10 = rfF.get .x15 := (spill_regs_core ro rwBase fp rfF wsF rf h13 hrf).1

private theorem spill_x11 (ro : Region) (rwBase fp : Word)
    (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (h13 : rfF.get .x13 = fp)
    (hrf : rf = (execBlock ro rwBase rfF wsF
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]).1) :
    rf.get .x11 = rfF.get .x17 := (spill_regs_core ro rwBase fp rfF wsF rf h13 hrf).2.1

private theorem spill_x12 (ro : Region) (rwBase fp : Word)
    (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (h13 : rfF.get .x13 = fp)
    (hrf : rf = (execBlock ro rwBase rfF wsF
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]).1) :
    rf.get .x12 = rfF.get .x12 := (spill_regs_core ro rwBase fp rfF wsF rf h13 hrf).2.2.1

private theorem spill_x13_direct (ro : Region) (rwBase : Word)
    (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (hrf : rf = (execBlock ro rwBase rfF wsF
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]).1) :
    rf.get .x13 = rfF.get .x13 + 32 := by
  have h32 : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
    storeSem, h32, RegFile.get_set_ne, RegFile.get_set_self,
    ne_eq, reduceCtorEq, not_false_eq_true]

private theorem spill_x28_direct (ro : Region) (rwBase : Word)
    (rfF : RegFile) (wsF : List (BitVec 8)) (rf : RegFile)
    (hrf : rf = (execBlock ro rwBase rfF wsF
      [.ADD .x7 .x15 .x17, .SD .x13 .x7 8, .SD .x13 .x16 16,
       .SD .x13 .x12 24, .MV .x10 .x15, .MV .x11 .x17,
       .ADDI .x13 .x13 32, .LI .x28 (0x1000 : Word)]).1) :
    rf.get .x28 = decEntry := by
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, loadSem,
    storeSem, RegFile.get_set_ne, RegFile.get_set_self,
    ne_eq, reduceCtorEq, not_false_eq_true]
  simpa [decEntry]

set_option maxRecDepth 8000 in
private theorem child_pre_sp_generic
    (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion)
    (beS childS : FnHandleS)
    (fn : Fn)
    (hfnRegion : fn.region = (⟨inBase, bs⟩ : Region))
    (hfnRw : fn.rw = itemsRw d fp)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hq : pEnd ≤ bs.length)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (hcE : childS.entry = decEntry)
    (hcPre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        decPreS bs inBase d (fp + 32) rf ws A → childS.pre rf ws A) :
    ∀ rf ws A,
      Stmt.sp fn.region fn.rw
        (.block "spill" [.ADD .x7 .x15 .x17, .SD .x13 .x7 8,
          .SD .x13 .x16 16, .SD .x13 .x12 24, .MV .x10 .x15,
          .MV .x11 .x17, .ADDI .x13 .x13 32,
          .LI .x28 (0x1000 : Word)])
        (fun rf ws A =>
          Stmt.sp fn.region fn.rw (.block "fit0" [.SUB .x6 .x16 .x15])
            (fun rf ws A =>
              Stmt.sp fn.region fn.rw (itemLenCascade beS)
                (fun rf ws A =>
                  ∃ i < bs.length,
                    decInv bs inBase d fp pStart pEnd v A₀ i rf ws A ∧
                      (Cond.bltu .x15 .x16).holds rf)
                rf ws A ∧ (Cond.beq .x14 .x0).holds rf)
            rf ws A ∧ ¬ (Cond.bltu .x6 .x17).holds rf)
        rf ws A →
      ∃ h ∈ [childS], rf.get .x28 = h.entry ∧ h.pre rf ws A := by
  intro rf ws A hpre
  rw [hfnRegion, hfnRw] at hpre
  rcases hpre with ⟨rfP, wsP, hlenP, hReach, hrf, hws⟩
  obtain ⟨hFitSp, hfit⟩ := hReach
  obtain ⟨rfF, wsF, hlenF, hMid, hrfP, hwsP⟩ := hFitSp
  obtain ⟨hCasc, hpz⟩ := hMid
  have hpz' : rfF.get .x14 = 0 := by
    simpa [Cond.holds] using hpz
  obtain ⟨e13, c, hc1, hclt, e15, e16, e12⟩ :=
    cascade_regs bs inBase d fp pStart pEnd v A₀ beS L hq hbePost
      rfF wsF A hCasc hpz'
  have h13P : rfP.get .x13 = rfF.get .x13 := by
    rw [hrfP]
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
      ne_eq, reduceCtorEq, not_false_eq_true]
  have h15P : rfP.get .x15 = rfF.get .x15 := by
    rw [hrfP]
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
      ne_eq, reduceCtorEq, not_false_eq_true]
  have h16P : rfP.get .x16 = rfF.get .x16 := by
    rw [hrfP]
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
      ne_eq, reduceCtorEq, not_false_eq_true]
  have h12P : rfP.get .x12 = rfF.get .x12 := by
    rw [hrfP]
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem, RegFile.get_set_ne, RegFile.get_set_self,
      ne_eq, reduceCtorEq, not_false_eq_true]
  have h6P : rfP.get .x6 = BitVec.ofNat 64 (pEnd - c) := by
    rw [hrfP]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    rw [RegFile.get_set_self _ _ _ (by decide), e16, e15]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h17 : BitVec.ofNat 64 (rfP.get .x17).toNat = rfP.get .x17 := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlen_le : (rfP.get .x17).toNat ≤ pEnd - c := by
    have hfit' := hfit
    simp only [Cond.holds] at hfit'
    rw [h6P, ← h17] at hfit'
    have hpc_lt : pEnd - c < 2 ^ 64 := by
      have hb := L.regWf.2.1
      change inBase.toNat + bs.length < 2 ^ 64 at hb
      have hbs : bs.length < 2 ^ 64 := by omega
      have hpc : pEnd - c ≤ bs.length := by omega
      omega
    have hlen_lt : (rfP.get .x17).toNat < 2 ^ 64 := (rfP.get .x17).isLt
    simp only [Cond.holds, BitVec.ult, decide_eq_true_eq,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc_lt,
      Nat.mod_eq_of_lt hlen_lt] at hfit'
    exact Nat.le_of_not_gt hfit'
  let ro := fn.region
  let rwBase := fn.rw.base
  have h10 := spill_x10 ro rwBase fp rfP wsP rf (h13P.trans e13) hrf
  have h11 := spill_x11 ro rwBase fp rfP wsP rf (h13P.trans e13) hrf
  have h12 := spill_x12 ro rwBase fp rfP wsP rf (h13P.trans e13) hrf
  have h13 := spill_x13_direct ro rwBase rfP wsP rf hrf
  have h28 := spill_x28_direct ro rwBase rfP wsP rf hrf
  have hent : rf.get .x28 = childS.entry := by
    exact h28.trans hcE.symm
  have hchild : childS.pre rf ws A := by
    apply hcPre
    change ∃ off len : Nat,
      rf.get .x10 = inBase + BitVec.ofNat 64 off ∧
      rf.get .x11 = BitVec.ofNat 64 len ∧
      rf.get .x12 = BitVec.ofNat 64 d ∧
      rf.get .x13 = fp + 32 ∧ off + len ≤ bs.length
    refine ⟨c, (rfP.get .x17).toNat, ?_, ?_, ?_, ?_, ?_⟩
    · exact h10.trans (h15P.trans e15)
    · exact h11.trans h17.symm
    · exact h12.trans (h12P.trans e12)
    · rw [h13, h13P, e13]
    · omega
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨childS, rfl, hent, hchild⟩

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
  case rlpitems.iloop.body.ib0.mem =>
    rintro rf ws A hws ⟨i, hif, ⟨c, hc1, hc2, hci, h15, h16, h12, h13, htake,
      hlen', hA, hst⟩, hguard⟩
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hclt : c < pEnd := (guard_iff inBase c pEnd rf h15 h16 (by omega)
      hc2).mp hguard
    have hcb : c < bs.length := by omega
    have haddr : rf.get .x15 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 c := by
      rw [se12_0, h15]
      bv_omega
    have hnorw : ¬ inRw fp ws (rf.get .x15 + signExtend12 (0 : BitVec 12))
        1 := by
      rw [haddr]
      exact L.not_inRw hlen' hcb
    simp only [itemsFnV', itemsRw, blockVCs, loadSem, storeSem]
    refine ⟨?_, trivial, trivial, trivial⟩
    rw [if_neg hnorw, haddr]
    exact region_loadOk1 L.regWf hcb
  case rlpitems.post =>
    rintro rf ws A ⟨rfW, wsW, hlW, ⟨⟨i, hile, ⟨c, hc1, hc2, hci, h15, h16,
      h12, h13, htake, hlen', hA, hst⟩⟩, hncond⟩, hrf, hws2⟩
    subst hrf
    have hws' : ws = wsW := hws2
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hce : c = pEnd := by
      by_contra hne
      exact hncond ((guard_iff inBase c pEnd rfW h15 h16 (by omega) hc2).mpr
        (by omega))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      rcases hst with ⟨h14, hiff⟩ | ⟨h14, hnone, -⟩
      · rw [h14]
        have hrem : EvmAsm.EL.RLP.Ref.decodeJoinedEncodingsD d
            (EvmAsm.EL.RLP.Ref.win bs c (pEnd - c)) = some [] := by
          rw [hce, Nat.sub_self]
          exact EvmAsm.EL.RLP.Ref.joinedD_nil d bs pEnd
        have hfull : (EvmAsm.EL.RLP.Ref.decodeJoinedEncodingsD d
            (EvmAsm.EL.RLP.Ref.win bs pStart (pEnd - pStart))).isSome := by
          rw [← hiff, hrem]
          rfl
        unfold itemsStatus
        rw [if_pos hfull]
      · rw [h14]
        unfold itemsStatus
        rw [if_neg (by rw [hnone]; simp)]
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact h13
    · rw [hws']
      exact htake
    · exact hA
  case rlpitems.iloop.body.i1.e.i2.e.i3.t.ibtr.t.ibb1.mem =>
    rintro rf ws A hws ⟨⟨rf3, ws3, hl3, ⟨hR3, h3t⟩, hrf, hws3⟩, htr⟩
    obtain ⟨rf2, ws2, hl2, ⟨hR2, hn2⟩, hrf3, hws32⟩ := hR3
    obtain ⟨rf1, ws1, hl1, ⟨hR1, hn1⟩, hrf2, hws21⟩ := hR2
    obtain ⟨rfI, wsI, hlI, ⟨i, hif, ⟨c, hc1, hc2, hci, h15, h16, h12, h13,
      htake, hlen', hA, hst⟩, hguard⟩, hrf1, hws1I⟩ := hR1
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hclt : c < pEnd := (guard_iff inBase c pEnd rfI h15 h16 (by omega)
      hc2).mp hguard
    have haddr0 : rfI.get .x15 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 c := by
      rw [se12_0, h15]
      bv_omega
    have hnorwI : ¬ inRw fp wsI
        (rfI.get .x15 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr0]
      exact L.not_inRw hlI (by omega)
    rw [hrf1] at hrf2
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil] at hrf2
    rw [execInstrRF_lbu_ro2 _ _ _ _ _ _ _ hnorwI] at hrf2
    simp only [execInstrRF, aluSem] at hrf2
    rw [haddr0, region_byteAt L.regWf (by omega : c < bs.length)] at hrf2
    subst hrf2
    rw [hrf3] at hrf
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrf
    subst hrf
    simp only [Cond.holds, RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_nB7] at hn2 h3t htr
    have hbyte := (bs.getD c 0).isLt
    have hcbhi : 0xB8 ≤ (bs.getD c 0).toNat := by
      revert hn2
      simp only [BitVec.ult, decide_eq_true_eq]
      intro hn2
      bv_omega
    have hll : (bs.getD c 0).toNat - 0xB7 < pEnd - c := by
      rw [h16, h15] at htr
      revert htr
      simp only [BitVec.ult, decide_eq_true_eq]
      intro htr
      bv_omega
    have hc1lt : c + 1 < bs.length := by omega
    simp only [itemsFnV', itemsRw, blockVCs, loadSem, storeSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    refine ⟨?_, trivial⟩
    have haddr : rfI.get .x15 + signExtend12 (1 : BitVec 12)
        = inBase + BitVec.ofNat 64 (c + 1) := by
      rw [se12_1, h15]
      bv_omega
    rw [if_neg (by rw [haddr]; exact L.not_inRw hws hc1lt), haddr]
    exact region_loadOk1 L.regWf hc1lt
  case rlpitems.iloop.body.i1.e.i2.e.i3.t.ibtr.t.ibz.e.ibbe.pre =>
    rintro rf ws A ⟨rfA, wsA, hlA, ⟨⟨rfB1, wsB1, hlB1,
      ⟨⟨rf3, ws3, hl3, ⟨hR3, h3t⟩, hrfB1, hwsB1⟩, htr⟩, hrfA, hwsA⟩, hnz⟩,
      hrfP, hwsP⟩
    obtain ⟨rf2, ws2, hl2, ⟨hR2, hn2⟩, hrf3, hws32⟩ := hR3
    obtain ⟨rf1, ws1, hl1, ⟨hR1, hn1⟩, hrf2, hws21⟩ := hR2
    obtain ⟨rfI, wsI, hlI, ⟨i, hif, ⟨c, hc1, hc2, hci, h15, h16, h12, h13,
      htake, hlen', hA, hst⟩, hguard⟩, hrf1, hws1I⟩ := hR1
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hclt : c < pEnd := (guard_iff inBase c pEnd rfI h15 h16 (by omega)
      hc2).mp hguard
    have haddr0 : rfI.get .x15 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 c := by
      rw [se12_0, h15]
      bv_omega
    have hnorwI : ¬ inRw fp wsI
        (rfI.get .x15 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr0]
      exact L.not_inRw hlI (by omega)
    rw [hrf1] at hrf2
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil] at hrf2
    rw [execInstrRF_lbu_ro2 _ _ _ _ _ _ _ hnorwI] at hrf2
    simp only [execInstrRF, aluSem] at hrf2
    rw [haddr0, region_byteAt L.regWf (by omega : c < bs.length)] at hrf2
    subst hrf2
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrf3
    rw [hrf3] at hrfB1 h3t
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrfB1
    -- byte-class facts from the branch trail
    simp only [Cond.holds, RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true] at hn2 h3t
    have hbyte := (bs.getD c 0).isLt
    have hcbhi : 0xB8 ≤ (bs.getD c 0).toNat := by
      revert hn2
      simp only [BitVec.ult, decide_eq_true_eq]
      intro hn2
      bv_omega
    have hcblo : (bs.getD c 0).toNat < 0xC0 := by
      revert h3t
      simp only [BitVec.ult, decide_eq_true_eq]
      intro h3t
      bv_omega
    -- projections of the ibb1-entry state
    have h15B1 : rfB1.get .x15 = inBase + BitVec.ofNat 64 c := by
      rw [hrfB1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact h15
    have h7B1 : rfB1.get .x7 = BitVec.ofNat 64 ((bs.getD c 0).toNat
        - 0xB7) := by
      rw [hrfB1]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true, se12_nB7]
      bv_omega
    have h6B1 : rfB1.get .x6 = BitVec.ofNat 64 (pEnd - c) := by
      rw [hrfB1]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      rw [h16, h15]
      bv_omega
    have hll : (bs.getD c 0).toNat - 0xB7 < pEnd - c := by
      have htr' := htr
      simp only [Cond.holds, h7B1, h6B1, BitVec.ult, decide_eq_true_eq,
        BitVec.toNat_ofNat] at htr'
      omega
    -- resolve the ibb1 LBU
    have haddr1 : rfB1.get .x15 + signExtend12 (1 : BitVec 12)
        = inBase + BitVec.ofNat 64 (c + 1) := by
      rw [se12_1, h15B1]
      bv_omega
    have hc1lt : c + 1 < bs.length := by omega
    have hnorw1 : ¬ inRw fp wsB1
        (rfB1.get .x15 + signExtend12 (1 : BitVec 12)) 1 := by
      rw [haddr1]
      exact L.not_inRw hlB1 hc1lt
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil] at hrfA
    rw [execInstrRF_lbu_ro2 _ _ _ _ _ _ _ hnorw1] at hrfA
    -- ibargs is pure ALU over rfA
    rw [hrfA] at hrfP
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrfP
    subst hrfP
    refine ⟨beS, by simp, ?_, ?_⟩
    · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      rw [hbeE]
      rfl
    · refine hbePre _ _ _ (c + 1) ((bs.getD c 0).toNat - 0xB7) ?_ ?_
        (by omega) (by omega)
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true, se12_1]
        rw [h15B1]
        bv_omega
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true]
        exact h7B1
  case rlpitems.iloop.body.i1.e.i2.e.i3.e.i4.e.iltr.t.ilb1.mem =>
    rintro rf ws A hws hre
    obtain ⟨hsp, htr⟩ := hre
    obtain ⟨rfE4, wsE4, hlE4, ⟨hSp3, hn4⟩, hrf, hws5⟩ := hsp
    obtain ⟨rfE3, wsE3, hlE3, ⟨hSp2, hn3⟩, hrfE4, hwsE4⟩ := hSp3
    obtain ⟨rfE2, wsE2, hlE2, ⟨hSp1, hn2⟩, hrfE3, hwsE3⟩ := hSp2
    obtain ⟨rfE1, wsE1, hlE1, ⟨hSp0, hn1⟩, hrfE2, hwsE2⟩ := hSp1
    obtain ⟨rfI, wsI, hlI, ⟨i, hif, ⟨c, hc1, hc2, hci, h15, h16, h12, h13,
      htake, hlen', hA, hst⟩, hguard⟩, hrfE1, hwsE1⟩ := hSp0
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hclt : c < pEnd := (guard_iff inBase c pEnd rfI h15 h16 (by omega)
      hc2).mp hguard
    have haddr0 : rfI.get .x15 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 c := by
      rw [se12_0, h15]
      bv_omega
    have hnorwI : ¬ inRw fp wsI
        (rfI.get .x15 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr0]
      exact L.not_inRw hlI (by omega)
    rw [hrfE1] at hrfE2
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil] at hrfE2
    rw [execInstrRF_lbu_ro2 _ _ _ _ _ _ _ hnorwI] at hrfE2
    simp only [execInstrRF, aluSem] at hrfE2
    rw [haddr0, region_byteAt L.regWf (by omega : c < bs.length)] at hrfE2
    subst hrfE2
    rw [hrfE3] at hrfE4
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrfE4
    rw [hrfE4] at hrf hn4
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrf
    subst hrf
    simp only [Cond.holds, RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_nF7] at hn4 htr
    have hbyte := (bs.getD c 0).isLt
    have hcbhi : 0xF8 ≤ (bs.getD c 0).toNat := by
      revert hn4
      simp only [BitVec.ult, decide_eq_true_eq]
      intro hn4
      bv_omega
    have hll : (bs.getD c 0).toNat - 0xF7 < pEnd - c := by
      rw [h16, h15] at htr
      revert htr
      simp only [BitVec.ult, decide_eq_true_eq]
      intro htr
      bv_omega
    have hc1lt : c + 1 < bs.length := by omega
    simp only [itemsFnV', itemsRw, blockVCs, loadSem, storeSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    refine ⟨?_, trivial⟩
    have haddr : rfI.get .x15 + signExtend12 (1 : BitVec 12)
        = inBase + BitVec.ofNat 64 (c + 1) := by
      rw [se12_1, h15]
      bv_omega
    rw [if_neg (by rw [haddr]; exact L.not_inRw hws hc1lt), haddr]
    exact region_loadOk1 L.regWf hc1lt
  case rlpitems.iloop.body.i1.e.i2.e.i3.e.i4.e.iltr.t.ilz.e.ilbe.pre =>
    rintro rf ws A ⟨rfA, wsA, hlA, ⟨⟨rfB1, wsB1, hlB1, ⟨hsp, htr⟩, hrfB1,
      hwsB1⟩, hnz⟩, hrfP, hwsP⟩
    obtain ⟨rfE4, wsE4, hlE4, ⟨hSp3, hn4⟩, hrfE5, hwsE5⟩ := hsp
    obtain ⟨rfE3, wsE3, hlE3, ⟨hSp2, hn3⟩, hrfE4, hwsE4⟩ := hSp3
    obtain ⟨rfE2, wsE2, hlE2, ⟨hSp1, hn2⟩, hrfE3, hwsE3⟩ := hSp2
    obtain ⟨rfE1, wsE1, hlE1, ⟨hSp0, hn1⟩, hrfE2, hwsE2⟩ := hSp1
    obtain ⟨rfI, wsI, hlI, ⟨i, hif, ⟨c, hc1, hc2, hci, h15, h16, h12, h13,
      htake, hlen', hA, hst⟩, hguard⟩, hrfE1, hwsE1⟩ := hSp0
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hclt : c < pEnd := (guard_iff inBase c pEnd rfI h15 h16 (by omega)
      hc2).mp hguard
    have haddr0 : rfI.get .x15 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 c := by
      rw [se12_0, h15]
      bv_omega
    have hnorwI : ¬ inRw fp wsI
        (rfI.get .x15 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr0]
      exact L.not_inRw hlI (by omega)
    rw [hrfE1] at hrfE2
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil] at hrfE2
    rw [execInstrRF_lbu_ro2 _ _ _ _ _ _ _ hnorwI] at hrfE2
    simp only [execInstrRF, aluSem] at hrfE2
    rw [haddr0, region_byteAt L.regWf (by omega : c < bs.length)] at hrfE2
    subst hrfE2
    rw [hrfE3] at hrfE4
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrfE4
    rw [hrfE4] at hrfE5 hn4
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrfE5
    simp only [Cond.holds, RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true] at hn4
    have hbyte := (bs.getD c 0).isLt
    have hcbhi : 0xF8 ≤ (bs.getD c 0).toNat := by
      revert hn4
      simp only [BitVec.ult, decide_eq_true_eq]
      intro hn4
      bv_omega
    have h15B1 : rfB1.get .x15 = inBase + BitVec.ofNat 64 c := by
      rw [hrfE5]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact h15
    have h7B1 : rfB1.get .x7 = BitVec.ofNat 64 ((bs.getD c 0).toNat
        - 0xF7) := by
      rw [hrfE5]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true, se12_nF7]
      bv_omega
    have h6B1 : rfB1.get .x6 = BitVec.ofNat 64 (pEnd - c) := by
      rw [hrfE5]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      rw [h16, h15]
      bv_omega
    have hll : (bs.getD c 0).toNat - 0xF7 < pEnd - c := by
      have htr' := htr
      simp only [Cond.holds, h7B1, h6B1, BitVec.ult, decide_eq_true_eq,
        BitVec.toNat_ofNat] at htr'
      omega
    have haddr1 : rfB1.get .x15 + signExtend12 (1 : BitVec 12)
        = inBase + BitVec.ofNat 64 (c + 1) := by
      rw [se12_1, h15B1]
      bv_omega
    have hc1lt : c + 1 < bs.length := by omega
    have hnorw1 : ¬ inRw fp wsB1
        (rfB1.get .x15 + signExtend12 (1 : BitVec 12)) 1 := by
      rw [haddr1]
      exact L.not_inRw hlB1 hc1lt
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil] at hrfB1
    rw [execInstrRF_lbu_ro2 _ _ _ _ _ _ _ hnorw1] at hrfB1
    rw [hrfB1] at hrfP
    simp only [itemsFnV', itemsRw, execBlock_cons, execBlock_nil,
      execInstrRF, aluSem] at hrfP
    subst hrfP
    refine ⟨beS, by simp, ?_, ?_⟩
    · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
      rw [hbeE]
      rfl
    · refine hbePre _ _ _ (c + 1) ((bs.getD c 0).toNat - 0xF7) ?_ ?_
        (by omega) (by omega)
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true, se12_1]
        rw [h15B1]
        bv_omega
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true]
        exact h7B1
  case rlpitems.iloop.body.pz.t.ifit.e.spill.mem =>
    rintro rf ws A hws ⟨⟨rfF, wsF, hlF, ⟨hCasc, hpz⟩, hrfS, hwsS⟩, hnfit⟩
    have hpz' : rfF.get .x14 = 0 := by
      have := hpz
      simpa [Cond.holds] using this
    obtain ⟨e13, c, hc1, hclt, e15, e16, e12⟩ :=
      cascade_regs bs inBase d fp pStart pEnd v A₀ beS L hq hbePost
        rfF wsF A hCasc hpz'
    exact spill_mem_core bs inBase d fp rfF wsF rf ws L.rwWf.2.1 hws e13
      hrfS
  case rlpitems.iloop.body.pz.t.ifit.e.child.pre =>
    exact child_pre_sp_generic
      bs inBase d fp pStart pEnd v A₀ beS childS
      (itemsFnV' bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS)
      (itemsFnV'_region_eq bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS)
      (itemsFnV'_rw_eq bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS)
      L hq hbePost hcE hcPre
  case rlpitems.iloop.body.pz.t.ifit.e.reload.mem =>
    rintro rf ws A hws ⟨rf₁, ws₁, A₁, hPrior, h, hmem, hent, hpre₁, hpost₁⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    obtain ⟨-, h13P, -, -⟩ := hcPost _ _ _ _ _ _ hpost₁
    exact reload_mem_core bs inBase d fp rf ws L.rwWf.2.1 hws h13P
  case rlpitems.iloop.inv_step =>
    intro i hi rf' ws' A' hsp
    exact itemsStep bs inBase d fp pStart pEnd v A₀ beS childS i L hq
      hbePost hcE hcPre hcPost rf' ws' A' hsp
  all_goals try decide

end EvmAsm.Rv64.SAsm.RecDecode
