/-
  EvmAsm.Codegen.Programs.U256DivU64BeInPlaceSAsm

  Exact-alias contract and proof for the restoring u256/u64 divider.
  The shared model and disjoint-buffer contract live in
  U256DivU64BeSAsm; this sibling keeps the alias-specific proof under the
  Codegen/Programs file-size cap.
-/

import EvmAsm.Codegen.Programs.U256DivU64BeSAsm

set_option maxRecDepth 8000

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace U256DivU64BeSAsm


/-! ## Alias-safe in-place contract (`srcPtr = outPtr`)

The linked K73 routine invokes this helper with the same pointer in `a0` and
`a2`.  The emitted loop is safe for that exact alias: it loads byte `i`,
computes the quotient byte, stores byte `i`, and only then advances to `i+1`.
The exact-alias case is not a general overlap theorem.  With a partial overlap,
a store at output offset `i` can overwrite a later source byte `j > i` before
that byte is read.  Thus the safe caller premise is the three-way disjunction
`srcPtr = outPtr`, `srcPtr + 32 ≤ outPtr`, or `outPtr + 32 ≤ srcPtr`; the latter
two cases are the disjoint-buffer premise of `u256DivU64BeFlat_spec` above.
This section supplies the second theorem for the live exact-alias call shape,
while the original theorem remains available for the two disjoint shapes. -/

private theorem getD_set_ne_in_place {l : List (BitVec 8)} {i j : Nat}
    {b d : BitVec 8} (h : i ≠ j) :
    (l.set i b).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h,
    List.getD_eq_getElem?_getD]

private theorem divState_length_in_place
    (a orig : List (BitVec 8)) (b : Word) (k : Nat) :
    (divState a orig b k).1.length = orig.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [divState_succ]
      simp only [List.length_set, ih]

private theorem divState_unprocessed_in_place
    (a : List (BitVec 8)) (b : Word) (k j : Nat)
    (hj : k ≤ j) (hji : j < 32) :
    (divState a a b k).1.getD j 0 = a.getD j 0 := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
      rw [divState_succ]
      rw [getD_set_ne_in_place (by omega : k ≠ j)]
      exact ih j (by omega) hji

def u256DivU64BeInPlaceInv (ptr b : Word)
    (aBytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun k rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    rf.get .x5 = (divState aBytes aBytes b k).2 ∧
    rf.get .x6 = BitVec.ofNat 64 k ∧ rf.get .x7 = (32 : Word) ∧
    ws = (divState aBytes aBytes b k).1 ∧ k ≤ 32 ∧
    0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧ aBytes.length = 32 ∧
    ptr.toNat + 32 < 2 ^ 64 ∧ A = empAssertion

def u256DivU64BeInPlaceLoopPost (ptr b : Word)
    (aBytes : List (BitVec 8)) : Reach :=
  fun rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    rf.get .x5 = u256DivU64BeRemainder aBytes aBytes b ∧
    rf.get .x6 = (32 : Word) ∧ rf.get .x7 = (32 : Word) ∧
    ws = u256DivU64BeQuotBytes aBytes aBytes b ∧ A = empAssertion

def u256DivU64BeInPlaceInnerInv (ptr b : Word)
    (i : Nat) (byte rem q : Word) (j : Nat)
    (aBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    rf.get .x6 = BitVec.ofNat 64 i ∧ rf.get .x5 = rem ∧
    rf.get .x29 = byte ∧ rf.get .x7 = BitVec.ofNat 64 (8 - j) ∧
    rf.get .x31 = q ∧
    divByteStepAux byte b rem q (8 - j) =
      divByteStepWord (aBytes.getD i 0) b (divState aBytes aBytes b i).2 ∧
    ws = (divState aBytes aBytes b i).1 ∧ j ≤ 8 ∧
    0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧ aBytes.length = 32 ∧
    ptr.toNat + 32 < 2 ^ 64 ∧ A = empAssertion

def u256DivU64BeInPlaceBitsInvS (ptr b : Word)
    (aBytes : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Nat →
      RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ _ _ j rf ws A =>
    ∃ i byte rem q, i < 32 ∧
      rf₀.get .x6 = BitVec.ofNat 64 i ∧
      u256DivU64BeInPlaceInnerInv ptr b i byte rem q j aBytes rf ws A

def u256DivU64BeInPlaceLoopBody (ptr b : Word)
    (aBytes : List (BitVec 8)) : Stmt :=
  .block "addrRead" [.ADD .x28 .x10 .x6] ;;;
  .block "readA" [.LBU .x29 .x28 (0 : BitVec 12)] ;;;
  .block "divInit" [.LI .x31 (0 : Word), .LI .x7 (8 : Word)] ;;;
  .«whileS» "bits" (.bne .x7 .x0) 8
    (u256DivU64BeInPlaceBitsInvS ptr b aBytes) u256DivU64BeInnerBody ;;;
  .block "divStore"
    [.ADD .x28 .x12 .x6,
     .SB .x28 .x31 (0 : BitVec 12),
     .ADDI .x6 .x6 (1 : BitVec 12)]

def u256DivU64BeInPlaceBody (ptr b : Word)
    (aBytes : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x5 (0 : Word), .LI .x6 (0 : Word)] ;;;
  .whileHeader "loop"
    (.block "header" [.LI .x7 (32 : Word)])
    (.bne .x6 .x7)
    32
    (u256DivU64BeInPlaceInv ptr b aBytes)
    (u256DivU64BeInPlaceLoopBody ptr b aBytes) ;;;
  .block "retVal" [.MV .x10 .x5]

def u256DivU64BeInPlaceFn (ptr b : Word)
    (aBytes : List (BitVec 8)) : Fn where
  name := "u256DivU64BeInPlace"
  region := Region.empty
  rw := ⟨ptr, 32⟩
  pre := fun rf ws A =>
    rf.get .x10 = ptr ∧ rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    ws = aBytes ∧ 0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
    aBytes.length = 32 ∧ ptr.toNat + 32 < 2 ^ 64 ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = u256DivU64BeRemainder aBytes aBytes b ∧
    rf.get .x11 = b ∧ rf.get .x12 = ptr ∧
    ws = u256DivU64BeQuotBytes aBytes aBytes b ∧ A = empAssertion
  body := u256DivU64BeInPlaceBody ptr b aBytes

private theorem u256DivU64BeInPlaceBody_flatten_eq_generic :
    (u256DivU64BeInPlaceBody 0 1 []).flatten 0 ++
        [Instr.JALR .x0 .x1 (0 : BitVec 12)] =
      (u256DivU64BeBody 0 0 1 [] []).flatten 0 ++
        [Instr.JALR .x0 .x1 (0 : BitVec 12)] := by
  decide

theorem u256DivU64BeInPlaceBody_flatten (L : GuestLayout) :
    (u256DivU64BeInPlaceBody 0 1 []).flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] = u256DivU64Be_prog_of L := by
  rw [u256DivU64BeInPlaceBody_flatten_eq_generic]
  exact u256DivU64BeBody_flatten L

private theorem u256DivU64BeInPlaceFn_programRet_eq
    (ptr b : Word) (aBytes : List (BitVec 8)) :
    (u256DivU64BeInPlaceFn ptr b aBytes).programRet
        (GuestAddrs.u256_div_u64_be : Word) = u256DivU64Be_prog := by
  change (u256DivU64BeInPlaceBody 0 1 []).flatten 0 ++
      [Instr.JALR .x0 .x1 (0 : BitVec 12)] =
        u256DivU64Be_prog_of guestLayout
  rw [u256DivU64BeInPlaceBody_flatten guestLayout]

private theorem execBlock_lbu_rw_div (ptr : Word) (rf : RegFile)
    (ws aBytes : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (haddr : rf.get .x28 = ptr + BitVec.ofNat 64 i)
    (hws : ws = (divState aBytes aBytes (rf.get .x11) i).1)
    (hlen : aBytes.length = 32) :
    execBlock Region.empty ptr rf ws
      [.LBU .x29 .x28 (0 : BitVec 12)] =
      (rf.set .x29 ((aBytes.getD i 0).zeroExtend 64), ws) := by
  rw [execBlock_cons, execInstrRF_lbu_byte _ _ _ _ _ _ _ i
    (by
      rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
      bv_omega)
    (by
      rw [hws, divState_length_in_place, hlen]
      omega), execBlock_nil]
  rw [hws, divState_unprocessed_in_place aBytes (rf.get .x11) i i
    (by omega) hi]

private theorem readLbuRwDiv_blockVCs (ptr : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 32)
    (haddr : rf.get .x28 = ptr + BitVec.ofNat 64 i)
    (hws : ws.length = 32) :
    blockVCs Region.empty ptr rf ws
      [.LBU .x29 .x28 (0 : BitVec 12)] := by
  have haddr0 : rf.get .x28 + signExtend12 (0 : BitVec 12) =
      ptr + BitVec.ofNat 64 i := by
    rw [haddr, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw ptr ws (rf.get .x28 + signExtend12 (0 : BitVec 12)) 1
    then _ else Region.empty.loadOk _ _)
  rw [haddr0, if_pos]
  · unfold Region.loadOk
    change 1 ∣ (ptr + BitVec.ofNat 64 i - ptr).toNat ∧
      (ptr + BitVec.ofNat 64 i - ptr).toNat + 1 ≤ ws.length
    rw [add_idx_sub_self ptr i hi, hws]
    exact ⟨one_dvd _, by omega⟩
  · unfold inRw
    rw [add_idx_sub_self ptr i hi, hws]
    omega

private theorem u256DivU64BeInPlaceInnerLoopBody_effect
    (ptr b : Word) (aBytes : List (BitVec 8)) (j : Nat) :
    ∀ rf₀ ws₀ A₀ rf' ws' A',
      sp Region.empty ⟨ptr, 32⟩ u256DivU64BeInnerBody
        (fun rf ws A =>
          u256DivU64BeInPlaceBitsInvS ptr b aBytes
            rf₀ ws₀ A₀ j rf ws A ∧
          Cond.holds (.bne .x7 .x0) rf) rf' ws' A' →
      u256DivU64BeInPlaceBitsInvS ptr b aBytes
        rf₀ ws₀ A₀ (j + 1) rf' ws' A' := by
  intro rf₀ ws₀ A₀ rf' ws' A' hsp
  obtain ⟨rf, ws, hws, hpre, hrf', hws'⟩ := hsp
  obtain ⟨hbits, hguard⟩ := hpre
  obtain ⟨i, byte, rem, q, hi, hsnap, hinv⟩ := hbits
  obtain ⟨hx10, hx11, hx12, hx6, hx5, hx29, hx7, hx31, haux, hwsState,
    hjLe, hbPos, hbBound, hlenA, hptrBound, hA⟩ := hinv
  have hjLt : j < 8 := by
    simp only [Cond.holds] at hguard
    rw [hx7] at hguard
    by_contra hnot
    have hj8 : j = 8 := by omega
    subst hj8
    exact hguard rfl
  have he := innerBit_effect ptr rf ws byte rem q b
    (BitVec.ofNat 64 (8 - j)) hx11 hx5 hx7 hx29 hx31
  dsimp only at he
  refine ⟨i, byte <<< 1,
    (divBitStep ((byte >>> 7) &&& (1 : Word)) b rem).2,
    (q <<< 1) ||| (divBitStep ((byte >>> 7) &&& (1 : Word)) b rem).1,
    hi, hsnap, ?_⟩
  rcases he with ⟨hx10E, hx11E, hx12E, hx6E, hx5E, hx7E, hx29E,
    hx30E, hx31E, hwsE⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
    hbPos, hbBound, hlenA, hptrBound, hA⟩
  · rw [hrf']; exact hx10
  · rw [hrf']; exact hx11
  · rw [hrf']; exact hx12
  · rw [hrf']; exact hx6
  · rw [hrf']; exact hx5E
  · rw [hrf']; exact hx29E
  · rw [hrf']
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true]
    rw [hx7, show signExtend12 (-1 : BitVec 12) = (-1 : Word) by decide]
    have hnat : 8 - j = (8 - (j + 1)) + 1 := by omega
    rw [show BitVec.ofNat 64 (8 - j) =
      BitVec.ofNat 64 ((8 - (j + 1)) + 1) by rw [hnat]]
    simp only [BitVec.ofNat_add]
    bv_omega
  · rw [hrf']; exact hx31E
  · rw [show 8 - j = (8 - (j + 1)) + 1 by omega] at haux
    simpa [divByteStepAux] using haux
  · calc
      ws' = (execBlock Region.empty ptr rf ws
        [.SRLI .x28 .x5 63, .SLLI .x5 .x5 1, .SRLI .x30 .x29 7,
         .ANDI .x30 .x30 1, .SLLI .x29 .x29 1, .OR .x5 .x5 .x30,
         .SLTU .x30 .x5 .x11, .XORI .x30 .x30 1,
         .OR .x30 .x30 .x28, .SLLI .x31 .x31 1,
         .OR .x31 .x31 .x30, .SUB .x28 .x0 .x30,
         .AND .x28 .x28 .x11, .SUB .x5 .x5 .x28,
         .ADDI .x7 .x7 (-1 : BitVec 12)]).2 := hws'
      _ = ws := hwsE
      _ = (divState aBytes aBytes b i).1 := hwsState

private theorem u256DivU64BeInPlaceLoopBody_effect (ptr b : Word)
    (aBytes : List (BitVec 8)) (i : Nat) :
    ∀ rf' ws' A',
      sp Region.empty ⟨ptr, 32⟩
        (u256DivU64BeInPlaceLoopBody ptr b aBytes)
        (fun rf ws A =>
          u256DivU64BeInPlaceInv ptr b aBytes i rf ws A ∧
          Cond.holds (.bne .x6 .x7) rf) rf' ws' A' →
      rf'.get .x10 = ptr ∧
      rf'.get .x11 = b ∧
      rf'.get .x12 = ptr ∧
      rf'.get .x5 = (divState aBytes aBytes b (i + 1)).2 ∧
      rf'.get .x6 = BitVec.ofNat 64 (i + 1) ∧
      ws' = (divState aBytes aBytes b (i + 1)).1 ∧
      i < 32 ∧
      0 < b.toNat ∧ b.toNat < 2 ^ 64 ∧
      aBytes.length = 32 ∧ ptr.toNat + 32 < 2 ^ 64 ∧
      A' = empAssertion := by
  intro rf' ws' A' hsp
  unfold u256DivU64BeInPlaceLoopBody at hsp
  obtain ⟨rfS, wsS, hwsS, hreachBits, hrf', hws'⟩ := hsp
  obtain ⟨rfEntry, wsEntry, AEntry, hentry, ⟨j, hjLe, hbits⟩, hnot⟩ := hreachBits
  obtain ⟨i0, byte, rem, q, hi0, hsnap, hinv⟩ := hbits
  obtain ⟨rfD, wsD, hwsD, hreachD, hrfEntry, hwsEntry⟩ := hentry
  obtain ⟨rfA0, wsA0, hwsA0, hreach0, hrfA, hwsA⟩ := hreachD
  obtain ⟨rf0, ws0, hws0, ⟨hinv0, _hguard0⟩, hrf0, hws0eq⟩ := hreach0
  obtain ⟨hx10_0, hx11_0, hx12_0, hx5_0, hx6_0, hx7_0, hwsState0,
    hiLe0, hbPos0, hbBound0, hlenA0, hpl0, hA0⟩ := hinv0
  dsimp only [u256DivU64BeInPlaceFn] at hrfEntry hwsEntry hrfA hwsA hrf0 hws0eq
  have hi : i < 32 := by
    simp only [Cond.holds] at _hguard0
    rw [hx6_0, hx7_0] at _hguard0
    by_contra hnot
    have hi32 : i = 32 := by omega
    subst hi32
    exact _hguard0 rfl
  have haddrA : rfA0.get .x28 = ptr + BitVec.ofNat 64 i := by
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx10_0, hx6_0]
  have hwsAState : wsA0 = (divState aBytes aBytes b i).1 := by
    rw [hws0eq]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    exact hwsState0
  have hwsAState' : wsA0 =
      (divState aBytes aBytes (rfA0.get .x11) i).1 := by
    have hx11A : rfA0.get .x11 = b := by
      rw [hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq,
        not_false_eq_true]
      exact hx11_0
    rw [hx11A]
    exact hwsAState
  have hreadA : execBlock Region.empty ptr rfA0 wsA0
      [.LBU .x29 .x28 (0 : BitVec 12)] =
      (rfA0.set .x29 ((aBytes.getD i 0).zeroExtend 64), wsA0) := by
    apply execBlock_lbu_rw_div ptr rfA0 wsA0 aBytes i hi haddrA
    · exact hwsAState'
    · exact hlenA0
  have hsnapOuter : rfEntry.get .x6 = BitVec.ofNat 64 i := by
    rw [hrfEntry, hrfA, hreadA]
    rw [hrf0]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
      RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
    exact hx6_0
  have hiEq : i0 = i := by
    have hEq := hsnap.symm.trans hsnapOuter
    have hNat := congrArg BitVec.toNat hEq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hNat
    rw [Nat.mod_eq_of_lt (by omega : i0 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)] at hNat
    exact hNat
  subst i0
  obtain ⟨hx10, hx11, hx12, hx6, hx5, hx29, hx7, hx31, haux, hwsState,
    hjLe', hbPos, hbBound, hlenA, hptrBound, hA⟩ := hinv
  have hjEq : j = 8 := by
    simp only [Cond.holds] at hnot
    rw [hx7] at hnot
    by_contra hne
    have hjLt : j < 8 := by omega
    have hne0 : (BitVec.ofNat 64 (8 - j)) ≠ (0 : Word) := by
      intro hz
      have hz' := congrArg BitVec.toNat hz
      have hlt : 8 - j < 2 ^ 64 := by omega
      change (8 - j) % 2 ^ 64 = 0 at hz'
      rw [Nat.mod_eq_of_lt hlt] at hz'
      omega
    exact hnot hne0
  subst hjEq
  have hq : q = (divByteStepWord (aBytes.getD i 0)
      b (divState aBytes aBytes b i).2).1 := by
    have h := congrArg Prod.fst haux
    simpa [divByteStepAux] using h
  have hrem : rem = (divByteStepWord (aBytes.getD i 0)
      b (divState aBytes aBytes b i).2).2 := by
    have h := congrArg Prod.snd haux
    simpa [divByteStepAux] using h
  have hwsLen : wsS.length = 32 := by
    calc
      wsS.length = (divState aBytes aBytes b i).1.length :=
        congrArg List.length hwsState
      _ = aBytes.length := divState_length_in_place aBytes aBytes b i
      _ = 32 := hlenA
  have hstore := divStore_effect_early ptr rfS wsS i hi0 hx6 hx12 hwsLen
  dsimp only at hstore
  obtain ⟨hsx10, hsx11, hsx12, hsx5, hsx6, hsws⟩ := hstore
  dsimp only [RwRegion.base] at hrf' hws'
  subst hrf'
  subst hws'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hi0, hbPos, hbBound, hlenA,
    hptrBound, hA⟩
  · exact hsx10.trans hx10
  · exact hsx11.trans hx11
  · exact hsx12
  · calc
      _ = rfS.get .x5 := hsx5
      _ = rem := hx5
      _ = (divByteStepWord (aBytes.getD i 0)
          b (divState aBytes aBytes b i).2).2 := hrem
      _ = (divState aBytes aBytes b (i + 1)).2 := by
        rw [divState_succ]
        rfl
  · exact hsx6
  · rw [hsws, hwsState, divState_succ]
    simp [divByteStep, divByteStepWord, hx31, hq]

private theorem u256DivU64BeInPlace_retVal_post (ptr b : Word)
    (aBytes : List (BitVec 8)) :
    ∀ rf ws A,
      sp Region.empty ⟨ptr, 32⟩ (.block "retVal" [.MV .x10 .x5])
        (u256DivU64BeInPlaceLoopPost ptr b aBytes) rf ws A →
      (u256DivU64BeInPlaceFn ptr b aBytes).post rf ws A := by
  rintro rf ws A ⟨rf₀, ws₀, hws₀, hloop, hrf, hws⟩
  obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsBytes, hA⟩ := hloop
  subst hrf
  subst hws
  simp only [u256DivU64BeInPlaceFn, execBlock_cons, execBlock_nil, execInstrRF,
    aluSem]
  refine ⟨?_, ?_, ?_, hwsBytes, hA⟩
  · rw [RegFile.get_set_self _ _ _ (by decide), hx5]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
  · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]

theorem u256DivU64BeInPlace_spec (ptr b : Word)
    (aBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨ptr, 32⟩)
    (base : Word) :
    (u256DivU64BeInPlaceFn ptr b aBytes).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case u256DivU64BeInPlace.loop.inv_init =>
    rintro rf ws A ⟨rfH, wsH, hwsH, hinit, hrf, hws⟩
    obtain ⟨rf₀, ws₀, hws₀, hpre, hrfH, hwsH_eq⟩ := hinit
    obtain ⟨hx10, hx11, hx12, hwsOrig, hbPos, hbBound, hlenA, hpl, hA⟩ := hpre
    dsimp only [u256DivU64BeInPlaceFn] at hws₀ hwsH hrfH hwsH_eq hrf hws
    subst hrf
    subst hws
    subst hrfH
    subst hwsH_eq
    unfold u256DivU64BeInPlaceInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hbPos, hbBound, hlenA,
      hpl, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hwsOrig
  case u256DivU64BeInPlace.loop.inv_step =>
    rintro i hiLt rf' ws' A' hsp
    obtain ⟨rfB, wsB, hwsB, hbody, hrf', hws'⟩ := hsp
    dsimp only [u256DivU64BeInPlaceFn] at hbody hwsB hrf' hws'
    have hb := u256DivU64BeInPlaceLoopBody_effect ptr b aBytes i rfB wsB A' hbody
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hwsState, hik, hbPos, hbBound,
      hlenA, hpl, hA⟩ := hb
    subst hrf'
    subst hws'
    unfold u256DivU64BeInPlaceInv
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hbPos, hbBound, hlenA,
      hpl, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7), hx10]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx12]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), hx5]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7), hx6]
    · rw [RegFile.get_set_self _ _ _ (by decide)]
    · exact hwsState
  case u256DivU64BeInPlace.loop.exhausted =>
    rintro rf ws A hinv
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hiLe, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    simp only [Cond.holds]
    rw [hx6, hx7]
    intro h_ne
    exact h_ne rfl
  case u256DivU64BeInPlace.loop.body.readA.mem =>
    rintro rf ws A hws hreach
    obtain ⟨rf₀, ws₀, hws₀, ⟨i, hi, hinv, hguard⟩, hrf, hwsEq⟩ := hreach
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    dsimp only [u256DivU64BeInPlaceFn] at hrf hws hws₀ hwsEq ⊢
    have hws32 : ws.length = 32 := hws
    subst hrf
    subst hwsEq
    have haddr : (rf₀.set Reg.x28 (rf₀.get Reg.x10 + rf₀.get Reg.x6)).get
        Reg.x28 = ptr + BitVec.ofNat 64 i := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx10, hx6]
    exact readLbuRwDiv_blockVCs ptr _ ws i hi haddr hws32
  case u256DivU64BeInPlace.loop.body.divStore.mem =>
    rintro rf ws A hws hreach
    obtain ⟨_rfEntry, _wsEntry, _AEntry, _hentry,
      ⟨j, _hj, hbits⟩, _hnot⟩ := hreach
    obtain ⟨i, _byte, _rem, _q, hi, _hsnap, hinv⟩ := hbits
    obtain ⟨_hx10, _hx11, hx12, hx6, _hx5, _hx29, _hx7, _hx31,
      _haux, _hwsState, _hjLe, _hbPos, _hbBound, _hlenA,
      _hptrBound, _hA⟩ := hinv
    exact divStore_blockVCs ptr rf ws i hi hx6 hx12 hws
  case u256DivU64BeInPlace.loop.body.bits.inv_init =>
    rintro rf ws A hsp
    obtain ⟨rfD, wsD, hwsD, hreachD, hrf, hws⟩ := hsp
    obtain ⟨rfA0, wsA0, hwsA0, hreachA, hrfA, hwsA⟩ := hreachD
    obtain ⟨rf0, ws0, hws0, hreach0, hrf0, hws0eq⟩ := hreachA
    obtain ⟨i, hi, hinv0, hguard0⟩ := hreach0
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState,
      hiLe, hbPos, hbBound, hlenA, hptrBound, hA0⟩ := hinv0
    dsimp only [u256DivU64BeInPlaceFn] at hrf hws hrfA hwsA hrf0 hws0eq
    have hiLt : i < 32 := by
      simp only [Cond.holds] at hguard0
      rw [hx6, hx7] at hguard0
      by_contra hnot
      have hi32 : i = 32 := by omega
      subst hi32
      exact hguard0 rfl
    have haddrA : rfA0.get .x28 = ptr + BitVec.ofNat 64 i := by
      rw [hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hx10, hx6]
    have hwsAState : wsA0 = (divState aBytes aBytes b i).1 := by
      rw [hws0eq]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      exact hwsState
    have hwsAState' : wsA0 =
        (divState aBytes aBytes (rfA0.get .x11) i).1 := by
      have hx11A : rfA0.get .x11 = b := by
        rw [hrf0]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
          RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        exact hx11
      rw [hx11A]
      exact hwsAState
    have hreadA : execBlock Region.empty ptr rfA0 wsA0
        [.LBU .x29 .x28 (0 : BitVec 12)] =
        (rfA0.set .x29 ((aBytes.getD i 0).zeroExtend 64), wsA0) := by
      apply execBlock_lbu_rw_div ptr rfA0 wsA0 aBytes i hiLt haddrA
      · exact hwsAState'
      · exact hlenA
    have hx10D : rfD.get .x10 = ptr := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : .x10 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        ]
      exact hx10
    have hx11D : rfD.get .x11 = b := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : .x11 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        ]
      exact hx11
    have hx12D : rfD.get .x12 = ptr := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : .x12 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        ]
      exact hx12
    have hx5D : rfD.get .x5 = (divState aBytes aBytes b i).2 := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : .x5 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx5
    have hx6D : rfD.get .x6 = BitVec.ofNat 64 i := by
      rw [hrfA, hreadA, RegFile.get_set_ne _ _ _ _ (by decide : .x6 ≠ .x29), hrf0]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx6
    have hx29D : rfD.get .x29 = (aBytes.getD i 0).zeroExtend 64 := by
      rw [hrfA, hreadA, RegFile.get_set_self _ _ _ (by decide)]
    have hwsDState : wsD = (divState aBytes aBytes b i).1 := by
      rw [hwsA, execBlock_lbu_ws, hws0eq]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      exact hwsState
    have hx10R : rf.get .x10 = ptr := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx10D
    have hx11R : rf.get .x11 = b := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx11D
    have hx12R : rf.get .x12 = ptr := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx12D
    have hx5R : rf.get .x5 = (divState aBytes aBytes b i).2 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx5D
    have hx6R : rf.get .x6 = BitVec.ofNat 64 i := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx6D
    have hx29R : rf.get .x29 = (aBytes.getD i 0).zeroExtend 64 := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx29D
    have hx7R : rf.get .x7 = (8 : Word) := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
    have hx31R : rf.get .x31 = (0 : Word) := by
      rw [hrf]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
        RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
    have hwsR : ws = (divState aBytes aBytes b i).1 := by
      rw [hws, hwsDState]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨i, (aBytes.getD i 0).zeroExtend 64,
      (divState aBytes aBytes b i).2, 0, hiLt, hx6R, ?_⟩
    refine ⟨hx10R, hx11R, hx12R, hx6R, hx5R, hx29R, hx7R, hx31R,
      ?_, hwsR, by omega, hbPos, hbBound, hlenA, hptrBound, hA0⟩
    simp [divByteStepWord]
  case u256DivU64BeInPlace.loop.body.bits.inv_step =>
    rintro rf₀ ws₀ A₀ hreach i hiLt rf' ws' A' hsp
    exact u256DivU64BeInPlaceInnerLoopBody_effect ptr b aBytes i
      rf₀ ws₀ A₀ rf' ws' A' hsp
  case u256DivU64BeInPlace.loop.body.bits.exhausted =>
    rintro rf₀ ws₀ A₀ hreach rf ws A hbits
    obtain ⟨i, byte, rem, q, hi, hsnap, hinv⟩ := hbits
    obtain ⟨hx10, hx11, hx12, hx6, hx5, hx29, hx7, hx31, haux, hwsState,
      hjLe, hbPos, hbBound, hlenA, hptrBound, hA⟩ := hinv
    simp only [Cond.holds]
    rw [hx7]
    intro h_ne
    have hzero : (BitVec.ofNat 64 (8 - 8) : Word) = 0 := by decide
    exact h_ne hzero
  case u256DivU64BeInPlace.post =>
    intro rf ws A h
    unfold u256DivU64BeInPlaceFn u256DivU64BeInPlaceBody at h
    obtain ⟨rfLoop, wsLoop, hwsLoop, hloopExit, hrf, hws⟩ := h
    obtain ⟨⟨i, hiFuel, hinv⟩, hnotGuard⟩ := hloopExit
    obtain ⟨hx10, hx11, hx12, hx5, hx6, hx7, hwsState, hik, hbPos,
      hbBound, hlenA, hpl, hA⟩ := hinv
    have heq : rfLoop.get .x6 = rfLoop.get .x7 := by
      by_contra h_ne
      exact hnotGuard h_ne
    have hiEq : i = 32 := by
      have hto := congrArg BitVec.toNat heq
      have hiToNat : (BitVec.ofNat 64 i).toNat = i := by
        rw [BitVec.toNat_ofNat]
        omega
      rw [hx6, hx7, hiToNat,
        show ((32 : Word).toNat = 32) from by decide] at hto
      omega
    subst hiEq
    subst hrf
    subst hws
    unfold u256DivU64BeInPlaceFn
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [RegFile.get_set_self _ _ _ (by decide), hx5]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10), hx11]
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx12]
    · exact hwsState
    · exact hA

theorem u256DivU64BeInPlaceFlat_spec (ret ptr b : Word)
    (aBytes : List (BitVec 8))
    (hrw : RwRegion.wf ⟨ptr, 32⟩)
    (hlen : aBytes.length = 32)
    (hptr : ptr.toNat + 32 < 2 ^ 64)
    (hbPos : 0 < b.toNat)
    (hsz : 4 * ((u256DivU64BeInPlaceFn ptr b aBytes).body.size + 1)
      ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin
      ((u256DivU64BeInPlaceFn ptr b aBytes).body.steps + 1)
      (GuestAddrs.u256_div_u64_be : Word) ret u256DivU64BeCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ b) **
        (.x12 ↦ᵣ ptr) ** regOwns u256DivU64BeScratch **
        bytesRegion ptr aBytes)
      (((.x1 : Reg) ↦ᵣ ret) **
        (.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes b) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ ptr) **
        regOwns u256DivU64BeScratch **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes b)) := by
  have hbBound : b.toNat < 2 ^ 64 := by omega
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns u256DivU64BeScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ ptr) **
        (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ ptr) ** bytesRegion ptr aBytes)
      (fun vf => ?_))
  have hpre : (u256DivU64BeInPlaceFn ptr b aBytes).pre
      (fun r => if r = .x10 then ptr else
        if r = .x11 then b else if r = .x12 then ptr else vf r)
      aBytes empAssertion := by
    refine ⟨?_, ?_, ?_, rfl, hbPos, hbBound, hlen, hptr, rfl⟩
    · show RegFile.get _ .x10 = ptr
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = b
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
    · show RegFile.get _ .x12 = ptr
      rw [RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x12 : Reg) ≠ .x10),
        if_neg (by decide : (Reg.x12 : Reg) ≠ .x11)]
      exact if_pos rfl
  have had := @Fn.retSpecFlat
    (u256DivU64BeInPlaceFn ptr b aBytes)
    (GuestAddrs.u256_div_u64_be : Word)
    (u256DivU64BeInPlace_spec ptr b aBytes hrw
      (GuestAddrs.u256_div_u64_be : Word))
    hsz ret halign
    (fun r => if r = .x10 then ptr else
      if r = .x11 then b else if r = .x12 then ptr else vf r)
    aBytes (by simpa [u256DivU64BeInPlaceFn] using hlen) hpre
    (((.x10 ↦ᵣ u256DivU64BeRemainder aBytes aBytes b) **
          (.x11 ↦ᵣ b) ** (.x12 ↦ᵣ ptr) **
          regOwns u256DivU64BeScratch) **
        bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes b))
    (fun _ _ _ hpost => hpost.2.2.2.2)
    (fun rf' ws' _hlen hpost hp hh => by
      obtain ⟨hx10', hx11', hx12', hws', _hA⟩ := hpost
      subst ws'
      have g10 : rf' .x10 = u256DivU64BeRemainder aBytes aBytes b := by
        rw [← hx10', RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      have g11 : rf' .x11 = b := by
        rw [← hx11', RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      have g12 : rf' .x12 = ptr := by
        rw [← hx12', RegFile.get, if_neg (by decide : (Reg.x12 : Reg) ≠ .x0)]
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_u256Div, g10, g11, g12] at hh
      rw [show (u256DivU64BeInPlaceFn ptr b aBytes).rw.base = ptr from rfl] at hh
      have hh1 :
          (((((((.x10 : Reg) ↦ᵣ u256DivU64BeRemainder aBytes aBytes b) **
            (.x11 ↦ᵣ b)) ** (.x12 ↦ᵣ ptr)) **
            bytesRegion ptr (u256DivU64BeQuotBytes aBytes aBytes b)) **
            regAtomsOf (fun r => rf' r) u256DivU64BeScratch) hp) := by
        xperm_hyp hh
      have hh2 := sepConj_mono_right
        (regAtomsOf_to_regOwns (fun r => rf' r) u256DivU64BeScratch) hp hh1
      xperm_hyp hh2)
  rw [u256DivU64BeInPlaceFn_programRet_eq ptr b aBytes] at had
  rw [show (u256DivU64BeInPlaceFn ptr b aBytes).region = Region.empty from rfl,
    show (u256DivU64BeInPlaceFn ptr b aBytes).rw.base = ptr from rfl,
    show Region.empty.base = (0 : Word) from rfl,
    show Region.empty.bytes = ([] : List (BitVec 8)) from rfl,
    bytesRegion_nil] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_u256Div,
    show (if (Reg.x10 : Reg) = .x10 then ptr else _) = ptr
      from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then ptr else
      if (Reg.x11 : Reg) = .x11 then b else _) = b from by
      rw [if_neg (by decide), if_pos rfl],
    show (if (Reg.x12 : Reg) = .x10 then ptr else
      if (Reg.x12 : Reg) = .x11 then b else
      if (Reg.x12 : Reg) = .x12 then ptr else _) = ptr from by
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl],
    regAtomsOf_congr
      (fun r => if r = .x10 then ptr else
        if r = .x11 then b else if r = .x12 then ptr else vf r)
      vf u256DivU64BeScratch
      (fun r hr => by
        obtain ⟨h10, h11, h12⟩ := u256Div_args_notin_scratch r hr
        show (if r = .x10 then ptr else
          if r = .x11 then b else if r = .x12 then ptr else vf r) = vf r
        rw [if_neg h10, if_neg h11, if_neg h12])] at had
  simp only [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end U256DivU64BeSAsm

end EvmAsm.Codegen
