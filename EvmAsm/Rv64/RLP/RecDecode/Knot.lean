/-
  EvmAsm.Rv64.RLP.RecDecode.Knot

  The recursion knot: the handle contracts of the decoder pair hold at
  every budget, by the mutual ladder

    DecSound 0           (items call arm dead: the budget check rejects)
    DecSound d  (fp+32)  ⟹  ItemsSound d fp    (child = widened decoder)
    ItemsSound d (fp+8)  ⟹  DecSound (d+1) fp  (items = widened loop)

  Each step packages the body specification (`decFnV_spec` /
  `itemsFnV_spec`) through `Fn.retSpecR` (the `ra`-spill wrapper) at the
  ghost-indexed pre/post families, and repackages the callee handles by
  `FnHandleS.widenPrefix` so the caller's own frame rides across the call.
-/

import EvmAsm.Rv64.RLP.RecDecode.ItemsBody

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open EvmAsm.EL.RLP (Byte)

-- ============================================================================
-- Small helpers
-- ============================================================================

/-- A dead snapshot handle with a chosen entry (unreachable call arms whose
    `entry` hypothesis is still demanded by the body spec). -/
def deadHandleSNE (entry : Word) (reg : Region) (rw : RwRegion) (n : Nat) :
    FnHandleS where
  entry := entry
  code := CodeReq.empty
  nSteps := n
  region := reg
  rw := rw
  pre := fun _ _ _ => False
  post := fun _ _ _ _ _ _ => False
  sound := fun _ _ _ _ _ hpre => hpre.elim

private theorem idxOf_ofNat (inBase : Word) (k bnd : Nat)
    (hk : k ≤ bnd) (hb : inBase.toNat + bnd < 2 ^ 64) :
    idxOf inBase (inBase + BitVec.ofNat 64 k) = k := by
  unfold idxOf
  have haddr : (inBase + BitVec.ofNat 64 k).toNat = inBase.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_sub, haddr]
  omega

/-- Shift a layout to an interior sub-window of the writable region. -/
theorem RdLayout.shift {inBase : Word} {bs : List Byte} {fp : Word}
    {bigLen : Nat} (L : RdLayout inBase bs fp bigLen)
    (k small : Nat) (hk8 : k % 8 = 0) (hks : k + small ≤ bigLen) :
    RdLayout inBase bs (fp + BitVec.ofNat 64 k) small := by
  have hw := L.rwWf
  have hal : fp.toNat % 8 = 0 := hw.1
  have hb2 : fp.toNat + bigLen < 2 ^ 64 := hw.2.1
  have hva : ∀ j, j < bigLen →
      isValidMemAddr (fp + BitVec.ofNat 64 j) = true := hw.2.2
  have hbase : (fp + BitVec.ofNat 64 k).toNat = fp.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨L.regWf, ⟨?_, ?_, ?_⟩, ?_⟩
  · show (fp + BitVec.ofNat 64 k).toNat % 8 = 0
    rw [hbase]
    omega
  · show (fp + BitVec.ofNat 64 k).toNat + small < 2 ^ 64
    rw [hbase]
    omega
  · intro j hj
    have hj' : j < small := hj
    have haddr : fp + BitVec.ofNat 64 k + BitVec.ofNat 64 j
        = fp + BitVec.ofNat 64 (k + j) := by
      bv_omega
    show isValidMemAddr (fp + BitVec.ofNat 64 k + BitVec.ofNat 64 j) = true
    rw [haddr]
    exact hva (k + j) (by omega)
  · rcases L.disj with h | h
    · left
      rw [hbase]
      omega
    · right
      rw [hbase]
      omega

-- ============================================================================
-- Code routing inside `decCr`
-- ============================================================================

private theorem rdbe_flatten_pin (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) :
    (readBeFn inBase bs rwBase rwLen).programRet rdbeEntry = rdbeProg := rfl

private theorem decCr_of_rdbe (a : Word) (i : Instr)
    (h : CodeReq.ofProg rdbeEntry rdbeProg a = some i) :
    decCr a = some i := by
  have hdecNone : CodeReq.ofProg decEntry decProg a = none := by
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hkk : kk < 9 := by
      rw [show rdbeProg.length = 9 from rfl] at hk
      exact hk
    apply CodeReq.ofProg_none_range
    intro k' hk2 heq
    have hkk2 : k' < 106 := by
      rw [show decProg.length = 106 from rfl] at hk2
      exact hk2
    have heq' : (0x800052ec : Word) + BitVec.ofNat 64 (4 * kk)
        = (0x80004fd0 : Word) + BitVec.ofNat 64 (4 * k') := heq
    exact absurd heq' (by bv_omega)
  have hitemsNone : CodeReq.ofProg itemsEntry itemsProg a = none := by
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hkk : kk < 9 := by
      rw [show rdbeProg.length = 9 from rfl] at hk
      exact hk
    apply CodeReq.ofProg_none_range
    intro k' hk2 heq
    have hkk2 : k' < 93 := by
      rw [show itemsProg.length = 93 from rfl] at hk2
      exact hk2
    have heq' : (0x800052ec : Word) + BitVec.ofNat 64 (4 * kk)
        = (0x80005178 : Word) + BitVec.ofNat 64 (4 * k') := heq
    exact absurd heq' (by bv_omega)
  simp only [decCr, CodeReq.union, hdecNone, hitemsNone, h]

-- ============================================================================
-- The read-BE leaf handle at a given frame
-- ============================================================================

private theorem rdbe_hsz (inBase : Word) (bs : List Byte) (rwBase : Word)
    (rwLen : Nat) :
    4 * ((readBeFn inBase bs rwBase rwLen).body.size + 1) ≤ 2 ^ 64 := by
  show 4 * ((readBeFn 0 [] 0 0).body.size + 1) ≤ 2 ^ 64
  decide +kernel

/-- The verified leaf, packaged for a caller with frame `⟨rwBase, rwLen⟩`. -/
def beHandleAt (inBase : Word) (bs : List Byte) (rwBase : Word) (rwLen : Nat)
    (L : RdLayout inBase bs rwBase rwLen) : FnHandleS :=
  readBeHandleS inBase bs rwBase rwLen L rdbeEntry
    (rdbe_hsz inBase bs rwBase rwLen)

private theorem beHandleAt_nSteps (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    (beHandleAt inBase bs rwBase rwLen L).nSteps = rdbeSteps := rfl

private theorem beHandleAt_code (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    ∀ a i, (beHandleAt inBase bs rwBase rwLen L).code a = some i →
      decCr a = some i := by
  intro a i h
  exact decCr_of_rdbe a i h

private theorem beHandleAt_pre (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion) (j n : Nat),
      rf.get .x29 = inBase + BitVec.ofNat 64 j →
      rf.get .x30 = BitVec.ofNat 64 n → n ≤ 8 → j + n ≤ bs.length →
      (beHandleAt inBase bs rwBase rwLen L).pre rf ws A :=
  fun _ _ _ j n h29 h30 hn hjn => ⟨j, n, h29, h30, hn, hjn⟩

private theorem beHandleAt_post (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen) :
    ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
      (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
      (beHandleAt inBase bs rwBase rwLen L).post rf₁ ws₁ A₁ rf ws A →
      rf.get .x31 = BitVec.ofNat 64
          (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
        ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
            rf.get r = rf₁.get r)
        ∧ ws = ws₁ ∧ A = A₁ :=
  fun _ _ _ _ _ _ h => h

private theorem beHandleAt_code_none (inBase : Word) (bs : List Byte)
    (rwBase : Word) (rwLen : Nat) (L : RdLayout inBase bs rwBase rwLen)
    (a : Word) (ha : a.toNat < rdbeEntry.toNat) :
    (beHandleAt inBase bs rwBase rwLen L).code a = none := by
  change CodeReq.ofProg rdbeEntry rdbeProg a = none
  apply CodeReq.ofProg_none_range_len rdbeEntry rdbeProg 9 a rfl
  intro k hk heq
  have hbase : rdbeEntry.toNat = 0x800052ec := rfl
  have haddr := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hbase] at haddr
  omega

set_option maxRecDepth 8000 in
private theorem decBody_callsOk (beS itemsS : FnHandleS)
  (hbeE : beS.entry = rdbeEntry) (hitE : itemsS.entry = itemsEntry)
    (hbeNone : ∀ a : Word, a.toNat < rdbeEntry.toNat → beS.code a = none) :
    (decBody beS itemsS).callsOk (decEntry + 4) := by
  and_intros
  all_goals first
    | (simp [Stmt.size, bytesArm, byteSingleArm, byteShortArm, byteLongArm,
        listArm, listShortHdr, listLongHdr, hbeE]; decide)
    | (simp [Stmt.size, bytesArm, byteSingleArm, byteShortArm, byteLongArm,
        listArm, listShortHdr, listLongHdr, hitE]; decide)
    | (apply hbeNone; simp [Stmt.size, bytesArm, byteSingleArm, byteShortArm,
        byteLongArm, listShortHdr]; decide)
    | trivial

set_option maxRecDepth 8000 in
private theorem itemsBody_callsOk (N : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS)
    (hbeE : beS.entry = rdbeEntry) (hcE : childS.entry = decEntry)
    (hbeNone : ∀ a : Word, a.toNat < rdbeEntry.toNat → beS.code a = none) :
    (itemsBody N inv beS childS).callsOk (itemsEntry + 4) := by
  and_intros
  all_goals first
    | (simp [Stmt.size, itemLenCascade, itemLongFormB, itemLongFormL,
        itemCallTail, itemsBodyStmt, hbeE]; decide)
    | (simp [Stmt.size, itemLenCascade, itemLongFormB, itemLongFormL,
        itemCallTail, itemsBodyStmt, hcE]; decide)
    | (apply hbeNone; simp [Stmt.size, itemLongFormB]; decide)
    | rfl
    | trivial

-- ============================================================================
-- The packaged decoder at a snapshot entry state
-- ============================================================================

private theorem se12k_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by
  decide

/-- The decoder `Fn` packaged at the snapshot ghosts `(rf₀, ws₀, A₀)`:
    the contract shape `Fn.retSpecR` consumes to produce `DecSound`. -/
private def decFnR (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (beS itemsS : FnHandleS) : Fn where
  name := "rlpdec"
  region := ⟨inBase, bs⟩
  rw := decRw d fp
  pre := Reach.exact rf₀ ws₀ A₀
  post := decPostS bs inBase d fp rf₀ ws₀ A₀
  body := decBody beS itemsS

private theorem dec_hsz (beS itemsS : FnHandleS) :
    4 * ((decBody beS itemsS).size + 3) ≤ 2 ^ 64 := by
  rw [show (decBody beS itemsS).size = decFnPin.body.size from rfl]
  decide +kernel

private theorem dec_hcode (beS itemsS : FnHandleS)
    (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (hbeE : beS.entry = rdbeEntry) (hitE : itemsS.entry = itemsEntry) :
    ∀ a i, CodeReq.ofProg decEntry
        ((decFnR bs inBase d fp rf₀ ws₀ A₀ beS itemsS).programRetR
          .x13 0 decEntry) a = some i →
      decCr a = some i := by
  intro a i h
  have hprog :
      (decFnR bs inBase d fp rf₀ ws₀ A₀ beS itemsS).programRetR
          .x13 0 decEntry = decProg := by
    change .SD .x13 .x1 0 ::
      ((decBody beS itemsS).flatten (decEntry + 4) ++
        [.LD .x1 .x13 0, .JALR .x0 .x1 0]) =
      .SD .x13 .x1 0 ::
        (decFnPin.body.flatten (decEntry + 4) ++
          [.LD .x1 .x13 0, .JALR .x0 .x1 0])
    rw [decBody_flatten beS itemsS hbeE hitE]
  rw [hprog] at h
  have h' : CodeReq.ofProg decEntry decProg a = some i := h
  simp only [decCr, CodeReq.union, h']

/-- The inner body of `DecSound` from the two handle contracts and the
    step budget. -/
private theorem decSound_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (beS itemsS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hbeE : beS.entry = rdbeEntry)
    (hbeCode : ∀ a i, beS.code a = some i → decCr a = some i)
    (hcalls : (decBody beS itemsS).callsOk (decEntry + 4))
    (hbeReg : beS.region = (⟨inBase, bs⟩ : Region))
    (hbeRw : beS.rw = decRw d fp)
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
    (hitE : itemsS.entry = itemsEntry)
    (hitCode : ∀ a i, itemsS.code a = some i → decCr a = some i)
    (hitReg : itemsS.region = (⟨inBase, bs⟩ : Region))
    (hitRw : itemsS.rw = decRw d fp)
    (hitPre : 1 ≤ d → ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsPreS bs inBase (d - 1) (fp + 8) rf ws A → itemsS.pre rf ws A)
    (hitPost : 1 ≤ d → ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = itemsStatus bs (pStartOf inBase rf₁)
            (pEndOf inBase rf₁ - pStartOf inBase rf₁) (d - 1)
          ∧ rf.get .x13 = fp + 8
          ∧ ws.take 8 = ws₁.take 8
          ∧ A = A₁)
    (hsteps : 1 + (decBody beS itemsS).steps + 2 ≤ decSteps bs.length d) :
    ∀ rf₀ ws₀ A₀, ws₀.length = 40 * d + 8 → Assertion.pcFree A₀ →
      decPreS bs inBase d fp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
        cpsTripleWithin (decSteps bs.length d) decEntry ret decCr
          (((.x1 : Reg) ↦ᵣ ret)
            ** asrtM ⟨inBase, bs⟩ (decRw d fp) (Reach.exact rf₀ ws₀ A₀))
          (((.x1 : Reg) ↦ᵣ ret)
            ** asrtM ⟨inBase, bs⟩ (decRw d fp)
                (decPostS bs inBase d fp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hpc hpre ret halign
  obtain ⟨off, len, hx10, hx11, hx12, hx13, hoff⟩ := hpre
  have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hfpb : fp.toNat + (40 * d + 8) < 2 ^ 64 := L.rwWf.2.1
  have hd64 : d < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have ho : offOf inBase rf₀ = off := by
    unfold offOf
    rw [hx10]
    exact idxOf_ofNat inBase off bs.length (by omega) hb
  have hl : lenOf rf₀ = len := by
    unfold lenOf
    rw [hx11, BitVec.toNat_ofNat]
    omega
  refine cpsTripleWithin_mono_nSteps hsteps ?_
  exact Fn.retSpecR (decFnR bs inBase d fp rf₀ ws₀ A₀ beS itemsS)
    decEntry decCr .x13 0 0
    (fun v => (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS).pre)
    (fun v => (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS).post)
    (by decide)
    L.rwWf
    ⟨0, rfl⟩
    (by show 0 + 8 ≤ 40 * d + 8; omega)
    (dec_hsz beS itemsS)
    (fun v => decFnV_spec bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS
      L hoff hx10 hx11 hx12 hx13 hd64 hbeE hbeCode hcalls hbeReg hbeRw hbePre
      hbePost hitE hitCode hitReg hitRw hitPre hitPost)
    (dec_hcode beS itemsS bs inBase d fp rf₀ ws₀ A₀ hbeE hitE)
    (by
      rintro rf ws A ⟨h1, -, -⟩
      rw [h1, hx13, se12k_0]
      show fp + 0 = fp + BitVec.ofNat 64 0
      bv_omega)
    (by
      rintro v rf ws A ⟨-, h13, -, -⟩
      rw [h13, se12k_0]
      show fp + 0 = fp + BitVec.ofNat 64 0
      bv_omega)
    (by
      rintro v rf ws A ⟨h1, h2, h3⟩ hwsl
      exact ⟨h1, by rw [h2], h3⟩)
    (by
      rintro v rf ws A ⟨h10, h13, -, hA⟩
      exact ⟨by rw [h10, ho, hl], h13, hA⟩)
    (by
      rintro v rf ws A ⟨-, -, htk, -⟩ hwsl
      rw [List.drop_zero]
      exact htk)
    ret halign

-- ============================================================================
-- The packaged items loop at a snapshot entry state
-- ============================================================================

/-- The items `Fn` packaged at the snapshot ghosts. -/
private def itemsFnR (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (beS childS : FnHandleS) : Fn where
  name := "rlpitems"
  region := ⟨inBase, bs⟩
  rw := itemsRw d fp
  pre := Reach.exact rf₀ ws₀ A₀
  post := itemsPostS bs inBase d fp rf₀ ws₀ A₀
  body := itemsBody bs.length (fun _ _ _ _ => True) beS childS

private theorem items_hsz (N : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS) :
    4 * ((itemsBody N inv beS childS).size + 3) ≤ 2 ^ 64 := by
  rw [show (itemsBody N inv beS childS).size = itemsFnPin.body.size from rfl]
  decide +kernel

private theorem decCr_of_items (a : Word) (i : Instr)
    (h : CodeReq.ofProg itemsEntry itemsProg a = some i) :
    decCr a = some i := by
  have hdecNone : CodeReq.ofProg decEntry decProg a = none := by
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hkk : kk < 93 := by
      rw [show itemsProg.length = 93 from rfl] at hk
      exact hk
    apply CodeReq.ofProg_none_range
    intro k' hk2 heq
    have hkk2 : k' < 106 := by
      rw [show decProg.length = 106 from rfl] at hk2
      exact hk2
    have heq' : (0x80005178 : Word) + BitVec.ofNat 64 (4 * kk)
        = (0x80004fd0 : Word) + BitVec.ofNat 64 (4 * k') := heq
    exact absurd heq' (by bv_omega)
  simp only [decCr, CodeReq.union, hdecNone, h]

private theorem items_hcode (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion)
    (beS childS : FnHandleS)
    (hbeE : beS.entry = rdbeEntry) (hcE : childS.entry = decEntry) :
    ∀ a i, CodeReq.ofProg itemsEntry
        ((itemsFnR bs inBase d fp rf₀ ws₀ A₀ beS childS).programRetR
          .x13 0 itemsEntry) a = some i →
      decCr a = some i := by
  intro a i h
  have hprog :
      (itemsFnR bs inBase d fp rf₀ ws₀ A₀ beS childS).programRetR
          .x13 0 itemsEntry = itemsProg := by
    change .SD .x13 .x1 0 ::
      ((itemsBody bs.length _ beS childS).flatten (itemsEntry + 4) ++
        [.LD .x1 .x13 0, .JALR .x0 .x1 0]) =
      .SD .x13 .x1 0 ::
        (itemsFnPin.body.flatten (itemsEntry + 4) ++
          [.LD .x1 .x13 0, .JALR .x0 .x1 0])
    rw [items_flatten_eq bs.length _ beS childS hbeE hcE]
  rw [hprog] at h
  have h' : CodeReq.ofProg itemsEntry itemsProg a = some i := h
  exact decCr_of_items a i h'

/-- The inner body of `ItemsSound` from the handle contracts and the step
    budget. -/
private theorem itemsSound_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (beS childS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hbeE : beS.entry = rdbeEntry)
    (hbeCode : ∀ a i, beS.code a = some i → decCr a = some i)
    (hcalls : (itemsBody bs.length (fun _ _ _ _ => True)
      beS childS).callsOk (itemsEntry + 4))
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
          ∧ A = A₁)
    (hsteps : 1 + (itemsBody bs.length (fun _ _ _ _ => True)
        beS childS).steps + 2 ≤ itemsSteps bs.length d) :
    ∀ rf₀ ws₀ A₀, ws₀.length = 40 * d + 40 → Assertion.pcFree A₀ →
      itemsPreS bs inBase d fp rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
        cpsTripleWithin (itemsSteps bs.length d) itemsEntry ret decCr
          (((.x1 : Reg) ↦ᵣ ret)
            ** asrtM ⟨inBase, bs⟩ (itemsRw d fp) (Reach.exact rf₀ ws₀ A₀))
          (((.x1 : Reg) ↦ᵣ ret)
            ** asrtM ⟨inBase, bs⟩ (itemsRw d fp)
                (itemsPostS bs inBase d fp rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hpc hpre ret halign
  obtain ⟨pStart, pEnd, hx15, hx16, hx12, hx13, hpq, hq⟩ := hpre
  have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hfpb : fp.toNat + (40 * d + 40) < 2 ^ 64 := L.rwWf.2.1
  have hd64 : d < 2 ^ 64 := by omega
  have hpS : pStartOf inBase rf₀ = pStart := by
    unfold pStartOf
    rw [hx15]
    exact idxOf_ofNat inBase pStart bs.length (by omega) hb
  have hpE : pEndOf inBase rf₀ = pEnd := by
    unfold pEndOf
    rw [hx16]
    exact idxOf_ofNat inBase pEnd bs.length (by omega) hb
  refine cpsTripleWithin_mono_nSteps hsteps ?_
  exact Fn.retSpecR (itemsFnR bs inBase d fp rf₀ ws₀ A₀ beS childS)
    itemsEntry decCr .x13 0 0
    (fun v => (itemsFnV bs inBase d fp pStart pEnd v rf₀ ws₀ A₀
      beS childS).pre)
    (fun v => (itemsFnV bs inBase d fp pStart pEnd v rf₀ ws₀ A₀
      beS childS).post)
    (by decide)
    L.rwWf
    ⟨0, rfl⟩
    (by show 0 + 8 ≤ 40 * d + 40; omega)
    (items_hsz bs.length _ beS childS)
    (fun v => itemsFnV_spec bs inBase d fp pStart pEnd v rf₀ ws₀ A₀
      beS childS L hpq hq hx15 hx16 hx12 hx13 hlen hd64 hbeE hbeCode hcalls
      hbeReg hbeRw hbePre hbePost hcE hcCode hcReg hcRw hcPre hcPost)
    (items_hcode bs inBase d fp rf₀ ws₀ A₀ beS childS hbeE hcE)
    (by
      rintro rf ws A ⟨h1, -, -⟩
      rw [h1, hx13, se12k_0]
      show fp + 0 = fp + BitVec.ofNat 64 0
      bv_omega)
    (by
      rintro v rf ws A ⟨-, h13, -, -⟩
      rw [h13, se12k_0]
      show fp + 0 = fp + BitVec.ofNat 64 0
      bv_omega)
    (by
      rintro v rf ws A ⟨h1, h2, h3⟩ hwsl
      exact ⟨h1, by rw [h2], h3⟩)
    (by
      rintro v rf ws A ⟨h10, h13, -, hA⟩
      exact ⟨by rw [h10, hpS, hpE], h13, hA⟩)
    (by
      rintro v rf ws A ⟨-, -, htk, -⟩ hwsl
      rw [List.drop_zero]
      exact htk)
    ret halign

-- ============================================================================
-- Step-budget accounting
-- ============================================================================

private theorem decBody_steps_pin (beS itemsS : FnHandleS) :
    (decBody beS itemsS).steps
      = (decBody (deadHandleSN Region.empty RwRegion.empty beS.nSteps)
          (deadHandleSN Region.empty RwRegion.empty itemsS.nSteps)).steps :=
  rfl

private theorem itemsBody_steps_pin (N : Nat)
    (inv : Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (beS childS : FnHandleS) :
    (itemsBody N inv beS childS).steps
      = (itemsBody N (fun _ _ _ _ => True)
          (deadHandleSN Region.empty RwRegion.empty beS.nSteps)
          (deadHandleSN Region.empty RwRegion.empty childS.nSteps)).steps :=
  rfl

private theorem decSteps_zero_bound (N : Nat) (beS itemsS : FnHandleS)
    (hbe : beS.nSteps = rdbeSteps) (hit : itemsS.nSteps = 0) :
    1 + (decBody beS itemsS).steps + 2 ≤ decSteps N 0 := by
  rw [decBody_steps_pin, hbe, hit]
  show _ ≤ (stepsPair N 0).1
  simp only [stepsPair]
  omega

private theorem decSteps_succ_bound (N d : Nat) (beS itemsS : FnHandleS)
    (hbe : beS.nSteps = rdbeSteps) (hit : itemsS.nSteps = itemsSteps N d) :
    1 + (decBody beS itemsS).steps + 2 ≤ decSteps N (d + 1) := by
  rw [decBody_steps_pin, hbe, hit]
  show _ ≤ (stepsPair N (d + 1)).1
  simp only [stepsPair, itemsSteps]
  omega

private theorem itemsSteps_bound (N d : Nat) (beS childS : FnHandleS)
    (hbe : beS.nSteps = rdbeSteps) (hc : childS.nSteps = decSteps N d) :
    1 + (itemsBody N (fun _ _ _ _ => True) beS childS).steps + 2
      ≤ itemsSteps N d := by
  rw [itemsBody_steps_pin, hbe, hc]
  show _ ≤ (stepsPair N d).2
  cases d with
  | zero =>
    simp only [stepsPair, decSteps]
    omega
  | succ d =>
    simp only [stepsPair, decSteps]
    omega

-- ============================================================================
-- The mutual ladder
-- ============================================================================

/-- Budget 0: the decoder rejects every list without calling the loop. -/
theorem decSound_zero (bs : List Byte) (inBase fp : Word) :
    DecSound bs inBase 0 fp := by
  intro L rf₀ ws₀ A₀ hlen hpc hpre ret halign
  exact decSound_core bs inBase 0 fp
    (beHandleAt inBase bs fp (40 * 0 + 8) L)
    (deadHandleSNE itemsEntry ⟨inBase, bs⟩ (decRw 0 fp) 0)
    L rfl (beHandleAt_code inBase bs fp (40 * 0 + 8) L)
      (decBody_callsOk
        (beHandleAt inBase bs fp (40 * 0 + 8) L)
        (deadHandleSNE itemsEntry ⟨inBase, bs⟩ (decRw 0 fp) 0)
        rfl rfl
        (fun a ha => beHandleAt_code_none inBase bs fp (40 * 0 + 8) L a ha))
      rfl rfl
    (beHandleAt_pre inBase bs fp (40 * 0 + 8) L)
    (beHandleAt_post inBase bs fp (40 * 0 + 8) L)
    rfl (fun a i h => nomatch h) rfl rfl
    (fun h1 => absurd h1 (by omega))
    (fun h1 => absurd h1 (by omega))
    (decSteps_zero_bound bs.length _ _ rfl rfl)
    rf₀ ws₀ A₀ hlen hpc hpre ret halign

/-- `ItemsSound d fp` from the decoder contract one frame deeper. -/
theorem itemsSound_step (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (ihdec : ∀ fp', DecSound bs inBase d fp') :
    ItemsSound bs inBase d fp := by
  intro L rf₀ ws₀ A₀ hlen hpc hpre ret halign
  have h32 : fp + BitVec.ofNat 64 32 = fp + 32 := rfl
  have L32 : RdLayout inBase bs (fp + 32) (40 * d + 8) :=
    h32 ▸ L.shift 32 (40 * d + 8) (by omega) (by omega)
  let childW : FnHandleS :=
    (decHandleSAt bs inBase d (fp + 32) L32
      (ihdec (fp + 32))).widenPrefix fp 32
      (by show fp + 32 = fp + BitVec.ofNat 64 32; rw [h32])
      ⟨4, rfl⟩ ⟨5 * d + 1, by show 40 * d + 8 = 8 * (5 * d + 1); omega⟩
      (fun rf ws ws' A h => h)
  refine itemsSound_core bs inBase d fp
    (beHandleAt inBase bs fp (40 * d + 40) L)
    childW
    L rfl (beHandleAt_code inBase bs fp (40 * d + 40) L)
      (itemsBody_callsOk bs.length (fun _ _ _ _ => True)
        (beHandleAt inBase bs fp (40 * d + 40) L) childW
        rfl rfl
        (fun a ha => beHandleAt_code_none inBase bs fp (40 * d + 40) L a ha))
      rfl rfl
    (beHandleAt_pre inBase bs fp (40 * d + 40) L)
    (beHandleAt_post inBase bs fp (40 * d + 40) L)
    rfl ?_ rfl ?_ ?_ ?_ ?_
    rf₀ ws₀ A₀ hlen hpc hpre ret halign
  · exact fun a i h => h
  · show (⟨fp, 32 + (40 * d + 8)⟩ : RwRegion) = itemsRw d fp
    show (⟨fp, 32 + (40 * d + 8)⟩ : RwRegion) = ⟨fp, 40 * d + 40⟩
    congr 1
    omega
  · exact fun rf ws A h => h
  · rintro rf₁ ws₁ A₁ rf ws A ⟨htk, hpost⟩
    obtain ⟨h10, h13, hA⟩ := hpost
    exact ⟨h10, h13, htk, hA⟩
  · exact itemsSteps_bound bs.length d _ _ rfl rfl

/-- `DecSound (d+1) fp` from the loop contract one frame deeper. -/
theorem decSound_succ (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (ihit : ∀ fp', ItemsSound bs inBase d fp') :
    DecSound bs inBase (d + 1) fp := by
  intro L rf₀ ws₀ A₀ hlen hpc hpre ret halign
  have h8 : fp + BitVec.ofNat 64 8 = fp + 8 := rfl
  have L8 : RdLayout inBase bs (fp + 8) (40 * d + 40) :=
    h8 ▸ L.shift 8 (40 * d + 40) (by omega) (by omega)
  let itemsW : FnHandleS :=
    (itemsHandleSAt bs inBase d (fp + 8) L8 (ihit (fp + 8))).widenPrefix fp 8
      (by show fp + 8 = fp + BitVec.ofNat 64 8; rw [h8])
      ⟨1, rfl⟩ ⟨5 * d + 5, by show 40 * d + 40 = 8 * (5 * d + 5); omega⟩
      (fun rf ws ws' A h => h)
  refine decSound_core bs inBase (d + 1) fp
    (beHandleAt inBase bs fp (40 * (d + 1) + 8) L)
    itemsW
    L rfl (beHandleAt_code inBase bs fp (40 * (d + 1) + 8) L)
      (decBody_callsOk
        (beHandleAt inBase bs fp (40 * (d + 1) + 8) L) itemsW
        rfl rfl
        (fun a ha => beHandleAt_code_none inBase bs fp (40 * (d + 1) + 8) L a ha))
      rfl rfl
    (beHandleAt_pre inBase bs fp (40 * (d + 1) + 8) L)
    (beHandleAt_post inBase bs fp (40 * (d + 1) + 8) L)
    rfl ?_ rfl ?_ ?_ ?_ ?_
    rf₀ ws₀ A₀ hlen hpc hpre ret halign
  · exact fun a i h => h
  · show (⟨fp, 8 + (40 * d + 40)⟩ : RwRegion) = decRw (d + 1) fp
    show (⟨fp, 8 + (40 * d + 40)⟩ : RwRegion) = ⟨fp, 40 * (d + 1) + 8⟩
    congr 1
    omega
  · intro h1 rf ws A hp
    exact hp
  · intro h1
    rintro rf₁ ws₁ A₁ rf ws A ⟨htk, hpost⟩
    obtain ⟨h10, h13, hA⟩ := hpost
    exact ⟨h10, h13, htk, hA⟩
  · exact decSteps_succ_bound bs.length d _ _ rfl rfl

/-- **The knot**: the decoder's handle contract holds at every budget. -/
theorem decSound_all (bs : List Byte) (inBase : Word) :
    ∀ (d : Nat) (fp : Word), DecSound bs inBase d fp := by
  intro d
  induction d with
  | zero => exact fun fp => decSound_zero bs inBase fp
  | succ d ih =>
    intro fp
    exact decSound_succ bs inBase d fp
      (fun fp' => itemsSound_step bs inBase d fp' (fun fp'' => ih fp''))

/-- The loop's handle contract at every budget. -/
theorem itemsSound_all (bs : List Byte) (inBase : Word) :
    ∀ (d : Nat) (fp : Word), ItemsSound bs inBase d fp :=
  fun d fp => itemsSound_step bs inBase d fp
    (fun fp' => decSound_all bs inBase d fp')

end RecDecode
end SAsm
end EvmAsm.Rv64
