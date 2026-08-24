/-
  EvmAsm.Rv64.RLP.RecDecode.Body

  The body specification of `rlp_decode`, proven per exact entry state
  (the shape `Fn.retSpecR`'s `hbody` consumes, and the shape the snapshot
  handle needs): from the post-prologue state — the entry registers naming
  the window `(off, len)` at budget `d`, the caller's return address `v`
  spilled in the frame slot — the body reaches its exit with
  `x14 = decStatus bs off len d`, `x13 = fp`, the slot intact, and the
  ambient untouched.

  The loop invariant at budget `d + 1` is `decInv` (the machine
  transcription of `decode_joined_encodings`' induction); at budget `0`
  the list arm rejects before the loop, so the instance's invariant is
  `False` — its `inv_init` mines the budget contradiction once and every
  other loop VC discharges trivially.
-/

import EvmAsm.Rv64.RLP.RecDecode.Widen
import EvmAsm.Rv64.RLP.RecDecode.VcgenK
import EvmAsm.Rv64.BitAux

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)
open EvmAsm.EL.RLP.Ref (decodeD decodeJoinedEncodingsD decodeItemLength win)

/-- The reader's returned value *is* the reference long-form length field:
    `beVal` and `EvmAsm.EL.RLP.Ref.winBE` share a body, so this holds by
    `rfl`.  Stated as a rewrite because `simp`/`simpa` close their goals at
    reducible transparency and therefore cannot bridge the two
    semireducible defs on their own. -/
private theorem beVal_eq_winBE (bs : List Byte) (j n : Nat) :
    beVal bs j n = EvmAsm.EL.RLP.Ref.winBE bs j n := rfl

/-- The ghost-indexed body post: status for the entry window, frame
    pointer and `ra` slot intact, ambient untouched. -/
def decPostV (bs : List Byte) (_inBase : Word) (d : Nat) (fp : Word)
    (off len : Nat) (v : Word) (A₀ : Assertion) : Reach :=
  fun rf ws A =>
    rf.get .x10 = decStatus bs off len d
    ∧ rf.get .x13 = fp
    ∧ ws.take 8 = dwordBytes v
    ∧ A = A₀

/-- The decoder `Fn` instance at full ghosts. -/
def decFnV (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (off len : Nat) (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (beS itemsS : FnHandleS) : Fn where
  name := "rlpdec"
  region := ⟨inBase, bs⟩
  rw := decRw d fp
  pre := Reach.exact rf₀ (setBytes ws₀ 0 (dwordBytes v)) A₀
  post := decPostV bs inBase d fp off len v A₀
  body := decBody beS itemsS

/-- The items `Fn` post at full ghosts. -/
def itemsPostV (bs : List Byte) (_inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) : Reach :=
  fun rf ws A =>
    rf.get .x10 = itemsStatus bs pStart (pEnd - pStart) d
    ∧ rf.get .x13 = fp
    ∧ ws.take 8 = dwordBytes v
    ∧ A = A₀

/-- The items `Fn` instance at full ghosts. -/
def itemsFnV (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (beS childS : FnHandleS) : Fn where
  name := "rlpitems"
  region := ⟨inBase, bs⟩
  rw := itemsRw d fp
  pre := Reach.exact rf₀ (setBytes ws₀ 0 (dwordBytes v)) A₀
  post := itemsPostV bs inBase d fp pStart pEnd v A₀
  body := itemsBody bs.length (decInv bs inBase d fp pStart pEnd v A₀)
    beS childS

set_option maxRecDepth 8000 in
theorem decBody_flatten (beS itemsS : FnHandleS)
    (hbeE : beS.entry = rdbeEntry) (hitE : itemsS.entry = itemsEntry) :
    (decBody beS itemsS).flatten (decEntry + 4)
      = decFnPin.body.flatten (decEntry + 4) := by
  simp [decBody, bytesArm, byteSingleArm, byteShortArm, byteLongArm,
    listArm, listShortHdr, listLongHdr, hbeE, hitE,
    decFnPin, deadHandleAtS, Stmt.flatten, Stmt.size]

private theorem decBodyFlat_len :
    (decFnPin.body.flatten (decEntry + 4)).length = 103 := rfl

set_option maxRecDepth 8000 in
private theorem decBody_calleesIn (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (beS itemsS : FnHandleS)
    (hbeCode : ∀ a i, beS.code a = some i → decCr a = some i)
    (hbeReg : beS.region = (⟨inBase, bs⟩ : Region))
    (hbeRw : beS.rw = decRw d fp)
    (hitCode : ∀ a i, itemsS.code a = some i → decCr a = some i)
    (hitReg : itemsS.region = (⟨inBase, bs⟩ : Region))
    (hitRw : itemsS.rw = decRw d fp) :
    (decBody beS itemsS).CalleesIn ⟨inBase, bs⟩ (decRw d fp) decCr := by
  and_intros
  all_goals trivial

/-- Low-bit masking is the identity on even words: the symbolic form of the
    call-site alignment side conditions (evaluating the flatten offsets
    inside a 200k-heartbeat budget is not affordable; parity is). -/
private theorem and_not_one_of_even (x : Word) (h : 2 ∣ x.toNat) :
    x &&& ~~~(1 : Word) = x := by
  apply BitAux.word_andn_one_of_even
  apply BitVec.eq_of_toNat_eq
  show x.toNat &&& 1 = 0
  rw [Nat.and_one_is_mod]
  omega

-- ============================================================================
-- Shared engine/arithmetic helpers for the VC cases
-- ============================================================================

private theorem se12_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
private theorem se12_n1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  decide
private theorem se12_8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_n8 : signExtend12 (-8 : BitVec 12) = (-8 : Word) := by
  decide
private theorem se12_n7F : signExtend12 (-0x7F : BitVec 12) = (-0x7F : Word) :=
  by decide
private theorem se12_n80 : signExtend12 (-0x80 : BitVec 12) = (-0x80 : Word) :=
  by decide
private theorem se12_nB7 : signExtend12 (-0xB7 : BitVec 12) = (-0xB7 : Word) :=
  by decide
private theorem se12_nBF : signExtend12 (-0xBF : BitVec 12) = (-0xBF : Word) :=
  by decide
private theorem se12_nC0 : signExtend12 (-0xC0 : BitVec 12) = (-0xC0 : Word) :=
  by decide
private theorem se12_nF7 : signExtend12 (-0xF7 : BitVec 12) = (-0xF7 : Word) :=
  by decide

private theorem word_sub_one_sub (a b : Nat) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) (hba : b < a) :
    (BitVec.ofNat 64 a : Word) + -1 - BitVec.ofNat 64 b =
      BitVec.ofNat 64 (a - 1 - b) := by
  rw [← BitVec.sub_eq_add_neg (BitVec.ofNat 64 a) (1 : Word)]
  have hone64 : (BitVec.ofNat 64 1).toNat = 1 := by
    simp [BitVec.toNat_ofNat]
  have h1 : (BitVec.ofNat 64 1 : Word) ≤ BitVec.ofNat 64 a := by
    rw [BitVec.ofNat_le_ofNat]
    simp only [Nat.mod_eq_of_lt ha]
    omega
  have hs : (BitVec.ofNat 64 a : Word) - 1 = BitVec.ofNat 64 (a - 1) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 a - BitVec.ofNat 64 1).toNat = _
    rw [BitVec.toNat_sub_of_le h1, BitVec.toNat_ofNat]
    rw [hone64]
    simp only [Nat.mod_eq_of_lt ha]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a - 1 < 2 ^ 64)]
  rw [hs]
  have h2 : BitVec.ofNat 64 b ≤ BitVec.ofNat 64 (a - 1) := by
    rw [BitVec.ofNat_le_ofNat]
    simp only [Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (by omega : a - 1 < 2 ^ 64)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le h2]
  simp only [BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (by omega : a - 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a - 1 - b < 2 ^ 64)]

private theorem nat_sub_one_add (d : Nat) (h : 1 ≤ d) : d - 1 + 1 = d :=
  Nat.sub_add_cancel h

private theorem succ_lt_of_two_le (off len n : Nat) (hoff : off + len ≤ n)
    (hlen : 1 < len) : off + 1 < n := by omega

private theorem decodeD_long_list_badlen_at (bs : List Byte) (off len d : Nat)
    (hoff : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hbig : 0x38 ≤ EvmAsm.EL.RLP.Ref.winBE bs (off + 1)
      ((bs.getD off 0).toNat - 0xF7))
    (hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0xF7)
      + EvmAsm.EL.RLP.Ref.winBE bs (off + 1)
        ((bs.getD off 0).toNat - 0xF7))
    (hd : 1 ≤ d) :
    EvmAsm.EL.RLP.Ref.decodeD d
      (EvmAsm.EL.RLP.Ref.win bs off len) = none := by
  have h := EvmAsm.EL.RLP.Ref.decodeD_long_list_badlen (d - 1)
    hoff hlo htr hz hbig hbad
  rw [nat_sub_one_add d hd] at h
  exact h

private theorem toNat_zx (b : BitVec 8) : (b.zeroExtend 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le b.isLt (by omega))

private theorem ult_iff (x y : Word) :
    (BitVec.ult x y = true) ↔ x.toNat < y.toNat := by
  simp [BitVec.ult]

/-- An `LBU` outside the writable window reads the read-only region. -/
private theorem lbu_ro (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd
          ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

private theorem addr_add (inBase : Word) (a b : Nat) :
    inBase + BitVec.ofNat 64 a + BitVec.ofNat 64 b
      = inBase + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- The `b0` block's engine result: load the head byte, stage `0xC0`. -/
private theorem b0_engine (bs : List Byte) (inBase fp : Word) (rwLen : Nat)
    (L : RdLayout inBase bs fp rwLen)
    (rf : RegFile) (ws : List (BitVec 8)) (hws : ws.length = rwLen)
    (off : Nat) (hx10 : rf.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) :
    execBlock ⟨inBase, bs⟩ fp rf ws
        [.LBU .x5 .x10 0, .LI .x6 0xC0]
      = ((rf.set .x5 ((bs.getD off 0).zeroExtend 64)).set .x6 0xC0, ws) := by
  have haddr : rf.get .x10 + signExtend12 (0 : BitVec 12)
      = inBase + BitVec.ofNat 64 off := by
    rw [se12_0, hx10]
    bv_omega
  have hnorw : ¬ inRw fp ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
    rw [haddr]
    exact L.not_inRw hws hoffb
  simp only [execBlock_cons, execBlock_nil]
  rw [lbu_ro _ _ _ _ _ _ _ hnorw]
  simp only [execInstrRF, aluSem]
  rw [haddr, region_byteAt L.regWf hoffb]

private theorem b0_x5 (bs : List Byte) (inBase fp : Word) (rwLen : Nat)
    (L : RdLayout inBase bs fp rwLen) (rf : RegFile)
    (ws : List (BitVec 8)) (hws : ws.length = rwLen)
    (off : Nat) (hx10 : rf.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) :
    ((execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1).get .x5 =
      (bs.getD off 0).zeroExtend 64 := by
  rw [b0_engine bs inBase fp rwLen L rf ws hws off hx10 hoffb]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true]

private theorem b0_ws (bs : List Byte) (inBase fp : Word)
    (rf : RegFile) (ws : List (BitVec 8)) :
    (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).2 = ws := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem]

private theorem ge_f8_of_short_blocks (b : Byte)
    (rfB0 rfCB rfB1 : RegFile) (y : Word)
    (hb0 : rfCB = (rfB0.set .x5 (b.zeroExtend 64)).set .x6 0xC0)
    (hcb : rfB1 = (rfCB.set .x12 y).set .x6 0xF8)
    (hshort : ¬ BitVec.ult (rfB1.get .x5) (rfB1.get .x6) = true) :
    0xF8 ≤ b.toNat := by
  rw [hcb] at hshort
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true] at hshort
  rw [hb0] at hshort
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true] at hshort
  rw [ult_iff, toNat_zx] at hshort
  have hb : b.toNat < 256 := b.isLt
  have hc : ((248 : Word)).toNat = 0xF8 := rfl
  rw [hc] at hshort
  omega

private theorem b0_post_rf (bs : List Byte) (inBase fp : Word) (rwLen : Nat)
    (L : RdLayout inBase bs fp rwLen) (rf rf' : RegFile)
    (ws _ws' : List (BitVec 8)) (hws : ws.length = rwLen)
    (off : Nat) (hx10 : rf.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length)
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1) :
    rf' = ((rf.set .x5 ((bs.getD off 0).zeroExtend 64)).set .x6 0xC0) := by
  rw [b0_engine bs inBase fp rwLen L rf ws hws off hx10 hoffb] at hrf
  exact hrf

private theorem b0_post_rf_of_eq (bs : List Byte) (inBase fp : Word)
    (rwLen : Nat) (L : RdLayout inBase bs fp rwLen)
    (rf rf0 rf' : RegFile) (ws ws' : List (BitVec 8))
    (hws : ws.length = rwLen) (off : Nat)
    (hx10 : rf0.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) (h_eq : rf = rf0)
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1) :
    rf' = ((rf0.set .x5 ((bs.getD off 0).zeroExtend 64)).set .x6 0xC0) := by
  rw [h_eq] at hrf
  exact b0_post_rf bs inBase fp rwLen L rf0 rf' ws ws' hws off hx10 hoffb hrf

private theorem ge_f8_of_short_block_exec (bs : List Byte) (inBase fp : Word)
    (b : Byte) (rfB0 rfCB rfB1 : RegFile)
    (wsCB : List (BitVec 8))
    (hb0 : rfCB = (rfB0.set .x5 (b.zeroExtend 64)).set .x6 0xC0)
    (hrfCB : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hshort : ¬ BitVec.ult (rfB1.get .x5) (rfB1.get .x6) = true) :
    0xF8 ≤ b.toNat := by
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem] at hrfCB
  exact ge_f8_of_short_blocks b rfB0 rfCB rfB1
    (rfCB.get .x12 + (-1 : Word)) hb0 hrfCB hshort

private theorem ge_f8_of_short_b0_cb (bs : List Byte) (inBase fp : Word)
    (rwLen : Nat) (L : RdLayout inBase bs fp rwLen)
    (rf₀ rfB0 rfCB rfB1 : RegFile)
    (wsB0 wsCB : List (BitVec 8)) (hwsB0 : wsB0.length = rwLen)
    (off : Nat) (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) (h1 : rfB0 = rf₀)
    (hrfB0 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrfCB : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hshort : ¬ BitVec.ult (rfB1.get .x5) (rfB1.get .x6) = true) :
    0xF8 ≤ (bs.getD off 0).toNat := by
  have hx10B0 : rfB0.get .x10 =
      inBase + BitVec.ofNat 64 off := by
    rw [h1]
    exact hx10
  have hx5exec := b0_x5 bs inBase fp rwLen L rfB0 wsB0 hwsB0
    off hx10B0 hoffb
  have hx5CB : rfCB.get .x5 =
      (bs.getD off 0).zeroExtend 64 := by
    calc
      rfCB.get .x5 =
          ((execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
            [.LBU .x5 .x10 0, .LI .x6 0xC0]).1).get .x5 :=
        congrArg (fun r : RegFile => r.get .x5) hrfB0
    _ = (bs.getD off 0).zeroExtend 64 := hx5exec
  have h := hshort
  rw [hrfCB] at h
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true] at h
  rw [hx5CB, ult_iff, toNat_zx] at h
  have hc : ((0xF8 : Word)).toNat = 0xF8 := rfl
  rw [hc] at h
  have hb : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  omega

private theorem b0_x5_of_eq (bs : List Byte) (inBase fp : Word)
    (rwLen : Nat) (L : RdLayout inBase bs fp rwLen)
    (rf rf₀ rf' : RegFile) (ws : List (BitVec 8))
    (hws : ws.length = rwLen) (off : Nat)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) (h_eq : rf = rf₀)
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1) :
    rf'.get .x5 = (bs.getD off 0).zeroExtend 64 := by
  have hx10' : rf.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [h_eq]
    exact hx10
  have hx5exec := b0_x5 bs inBase fp rwLen L rf ws hws off hx10' hoffb
  calc
    rf'.get .x5 =
        ((execBlock ⟨inBase, bs⟩ fp rf ws
          [.LBU .x5 .x10 0, .LI .x6 0xC0]).1).get .x5 :=
      congrArg (fun r : RegFile => r.get .x5) hrf
    _ = (bs.getD off 0).zeroExtend 64 := hx5exec

private theorem b0_x12_of_eq (bs : List Byte) (inBase fp : Word)
    (rwLen : Nat) (L : RdLayout inBase bs fp rwLen)
    (rf rf₀ rf' : RegFile) (ws : List (BitVec 8))
    (hws : ws.length = rwLen) (off : Nat)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) (h_eq : rf = rf₀)
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1) :
    rf'.get .x12 = rf₀.get .x12 := by
  rw [h_eq] at hrf
  rw [hrf, b0_engine bs inBase fp rwLen L rf₀ ws hws off hx10 hoffb]
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem b0_x5_of_set (b : Byte) (rf rf₀ : RegFile)
    (h : rf = (rf₀.set .x5 (b.zeroExtend 64)).set .x6 0xC0) :
    rf.get .x5 = b.zeroExtend 64 := by
  rw [h]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true]

private theorem b0_engine_rf (bs : List Byte) (inBase fp : Word)
    (rwLen : Nat) (L : RdLayout inBase bs fp rwLen)
    (rf : RegFile) (ws : List (BitVec 8)) (hws : ws.length = rwLen)
    (off : Nat) (hx10 : rf.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) :
    (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1 =
      ((rf.set .x5 ((bs.getD off 0).zeroExtend 64)).set .x6 0xC0) := by
  rw [b0_engine bs inBase fp rwLen L rf ws hws off hx10 hoffb]

private theorem ge_f8_from_cb (bs : List Byte) (inBase fp : Word)
    (b : Byte) (rfCB rfB1 : RegFile) (wsCB : List (BitVec 8))
    (hrfCB : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hx5 : rfCB.get .x5 = b.zeroExtend 64)
    (hshort : ¬ BitVec.ult (rfB1.get .x5) (rfB1.get .x6) = true) :
    0xF8 ≤ b.toNat := by
  rw [hrfCB] at hshort
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true] at hshort
  rw [hx5, ult_iff, toNat_zx] at hshort
  have hc : ((0xF8 : Word)).toNat = 0xF8 := rfl
  rw [hc] at hshort
  have hb : b.toNat < 256 := b.isLt
  omega

private theorem b0_ge_f8_from_cond (bs : List Byte) (inBase fp : Word)
    (rwLen : Nat) (L : RdLayout inBase bs fp rwLen)
    (rf₀ rfB0 rfCB : RegFile) (wsB0 : List (BitVec 8))
    (hwsB0 : wsB0.length = rwLen) (off : Nat)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hoffb : off < bs.length) (h1 : rfB0 = rf₀)
    (hrfB0 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (h : ¬ BitVec.ult (rfCB.get .x5) (0xF8 : Word) = true) :
    0xF8 ≤ (bs.getD off 0).toNat := by
  rw [h1] at hrfB0
  rw [b0_engine bs inBase fp rwLen L rf₀ wsB0 hwsB0 off hx10 hoffb]
    at hrfB0
  rw [hrfB0] at h
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true] at h
  rw [ult_iff, toNat_zx] at h
  have hc : ((0xF8 : Word)).toNat = 0xF8 := rfl
  rw [hc] at h
  have hb : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  omega

private theorem b0_get_x5 (b : Byte) (rfB0 rfCB : RegFile)
    (hb0 : rfCB = (rfB0.set .x5 (b.zeroExtend 64)).set .x6 0xC0) :
    rfCB.get .x5 = b.zeroExtend 64 := by
  rw [hb0]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true]

private theorem cb_get_x5 (bs : List Byte) (inBase fp : Word)
    (rfCB rfB1 : RegFile) (wsCB : List (BitVec 8))
    (hrfCB : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1) :
    rfB1.get .x5 = rfCB.get .x5 := by
  rw [hrfCB]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, ne_eq,
    reduceCtorEq, not_false_eq_true]

private theorem cb_get_x6 (bs : List Byte) (inBase fp : Word)
    (rfCB rfB1 : RegFile) (wsCB : List (BitVec 8))
    (hrfCB : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1) :
    rfB1.get .x6 = (0xF8 : Word) := by
  rw [hrfCB]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem addi_x7_preserves_x14 (bs : List Byte) (inBase fp : Word)
    (rf rf' : RegFile) (ws : List (BitVec 8))
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.ADDI .x7 .x5 (-0xF7)]).1) :
    rf'.get .x14 = rf.get .x14 := by
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem addi_x7_preserves_x13 (bs : List Byte) (inBase fp : Word)
    (rf rf' : RegFile) (ws : List (BitVec 8))
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.ADDI .x7 .x5 (-0xF7)]).1) :
    rf'.get .x13 = rf.get .x13 := by
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem sub_x12_preserves_x13 (bs : List Byte) (inBase fp : Word)
    (rf rf' : RegFile) (ws : List (BitVec 8))
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1) :
    rf'.get .x13 = rf.get .x13 := by
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem li_x14_preserves_x13 (bs : List Byte) (inBase fp : Word)
    (rf rf' : RegFile) (ws : List (BitVec 8))
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LI .x14 1]).1) :
    rf'.get .x13 = rf.get .x13 := by
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem one_le_of_x12_notzero (d : Nat) (rfCB rf₀ : RegFile)
    (hnot : ¬ rfCB.get .x12 = rfCB.get .x0)
    (hx12CB : rfCB.get .x12 = rf₀.get .x12)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d) :
    1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with hzero | hpos
  · apply False.elim
    apply hnot
    rw [hx12CB, hx12, hzero]
    simp
  · exact hpos

private structure B0ShortCtx where
  bs : List Byte
  inBase : Word
  fp : Word
  rf₀ : RegFile
  rfB0 : RegFile
  rfCB : RegFile
  rfB1 : RegFile
  wsB0 : List (BitVec 8)
  wsCB : List (BitVec 8)
  off : Nat
  hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off
  h1 : rfB0 = rf₀
  hrfB0 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
    [.LBU .x5 .x10 0, .LI .x6 0xC0]).1

private theorem b0_short_ctx_ge (q : B0ShortCtx) (rwLen : Nat)
    (L : RdLayout q.inBase q.bs q.fp rwLen)
    (hlenB0 : q.wsB0.length = rwLen)
    (hoffb : q.off < q.bs.length)
    (hrfCB : q.rfB1 = (execBlock ⟨q.inBase, q.bs⟩ q.fp q.rfCB q.wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hshort : ¬ BitVec.ult (q.rfB1.get .x5) (q.rfB1.get .x6) = true)
    :
    0xF8 ≤ (q.bs.getD q.off 0).toNat := by
  exact ge_f8_of_short_b0_cb q.bs q.inBase q.fp rwLen L
    q.rf₀ q.rfB0 q.rfCB q.rfB1 q.wsB0 q.wsCB hlenB0 q.off q.hx10 hoffb
    q.h1 q.hrfB0 hrfCB hshort

private theorem b0_short_ctx_x12 (q : B0ShortCtx) (rwLen : Nat)
    (L : RdLayout q.inBase q.bs q.fp rwLen)
    (hlenB0 : q.wsB0.length = rwLen) (hoffb : q.off < q.bs.length) :
    q.rfCB.get .x12 = q.rf₀.get .x12 := by
  rw [q.hrfB0, q.h1]
  rw [b0_engine q.bs q.inBase q.fp rwLen L q.rf₀ q.wsB0 hlenB0
    q.off q.hx10 hoffb]
  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem b0_x12_raw (bs : List Byte) (inBase fp : Word)
    (rf rf₀ rf' : RegFile) (ws : List (BitVec 8))
    (h_eq : rf = rf₀)
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1) :
    rf'.get .x12 = rf₀.get .x12 := by
  rw [h_eq] at hrf
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  split <;> simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

private theorem b0_x13_raw (bs : List Byte) (inBase fp : Word)
    (rf rf₀ rf' : RegFile) (ws : List (BitVec 8))
    (h_eq : rf = rf₀)
    (hrf : rf' = (execBlock ⟨inBase, bs⟩ fp rf ws
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1) :
    rf'.get .x13 = rf₀.get .x13 := by
  rw [h_eq] at hrf
  rw [hrf]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  split <;> simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

private def longHdrReach (bs : List Byte) (inBase fp : Word) (d : Nat)
    (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion) : Reach :=
  fun rf ws A =>
    (∃ rf₁ ws₁,
      ws₁.length = 40 * d + 8 ∧
        (((∃ r0 s0, s0.length = 40 * d + 8 ∧
            (Reach.exact rf₀ (setBytes ws₀ 0 (dwordBytes v)) A₀
                r0 s0 A ∧ ¬ (Cond.beq .x11 .x0).holds r0) ∧
            rf₁ = (execBlock ⟨inBase, bs⟩ fp r0 s0
              [.LBU .x5 .x10 0, .LI .x6 0xC0]).1 ∧
            ws₁ = (execBlock ⟨inBase, bs⟩ fp r0 s0
              [.LBU .x5 .x10 0, .LI .x6 0xC0]).2) ∧
          ¬ (Cond.bltu .x5 .x6).holds rf₁) ∧
        ¬ (Cond.beq .x12 .x0).holds rf₁) ∧
      rf = (execBlock ⟨inBase, bs⟩ fp rf₁ ws₁
        [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1 ∧
      ws = (execBlock ⟨inBase, bs⟩ fp rf₁ ws₁
        [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).2) ∧
    ¬ (Cond.bltu .x5 .x6).holds rf

private structure TransitionCtx where
  bs : List Byte
  inBase : Word
  fp : Word
  rwLen : Nat
  L : RdLayout inBase bs fp rwLen
  len : Nat
  off : Nat
  rfW : RegFile
  rfB1 : RegFile
  rfCB : RegFile
  rf₀ : RegFile
  rfB0 : RegFile
  wsB0 : List (BitVec 8)
  wsB1 : List (BitVec 8)
  wsCB : List (BitVec 8)
  hlenB0 : wsB0.length = rwLen
  h1 : rfB0 = rf₀
  hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off
  hoffb : off < bs.length
  hrfB0 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
    [.LBU .x5 .x10 0, .LI .x6 0xC0]).1
  hx11 : rf₀.get .x11 = BitVec.ofNat 64 len
  hrfB1 : rfW = (execBlock ⟨inBase, bs⟩ fp rfB1 wsB1
    [.ADDI .x7 .x5 (-0xF7)]).1
  hrfCB : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
    [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1
  hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat
  hlen : len < 2 ^ 64
  hltr : ¬ (BitVec.ult (rfW.get .x7) (rfW.get .x11) = true)

private theorem transition_len_le (q : TransitionCtx) :
    q.len ≤ (q.bs.getD q.off 0).toNat - 0xF7 := by
  have hx10B0 : q.rfB0.get .x10 =
      q.inBase + BitVec.ofNat 64 q.off := by
    rw [q.h1]
    exact q.hx10
  have hx5CB : q.rfCB.get .x5 =
      (q.bs.getD q.off 0).zeroExtend 64 := by
    calc
      q.rfCB.get .x5 =
          ((execBlock ⟨q.inBase, q.bs⟩ q.fp q.rfB0 q.wsB0
            [.LBU .x5 .x10 0, .LI .x6 0xC0]).1).get .x5 :=
        congrArg (fun r : RegFile => r.get .x5) q.hrfB0
      _ = (q.bs.getD q.off 0).zeroExtend 64 :=
        b0_x5 q.bs q.inBase q.fp q.rwLen q.L q.rfB0 q.wsB0 q.hlenB0
          q.off hx10B0 q.hoffb
  have hx11CB : q.rfCB.get .x11 = q.rf₀.get .x11 := by
    rw [q.hrfB0, q.h1]
    rw [b0_engine q.bs q.inBase q.fp q.rwLen q.L q.rf₀ q.wsB0
      q.hlenB0 q.off q.hx10 q.hoffb]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
  have h := q.hltr
  rw [q.hrfB1] at h
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true] at h
  rw [q.hrfCB] at h
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
    RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true] at h
  rw [hx5CB, hx11CB, q.hx11, se12_nF7] at h
  have hle : (0xF7 : Word) ≤ (q.bs.getD q.off 0).zeroExtend 64 := by
    change 0xF7 ≤ (q.bs.getD q.off 0).toNat
    exact le_trans (by norm_num) q.hgeF8
  have hsub :
      ((q.bs.getD q.off 0).zeroExtend 64 - (0xF7 : Word)).toNat =
        (q.bs.getD q.off 0).toNat - 0xF7 := by
    rw [BitVec.toNat_sub_of_le hle, toNat_zx]
    have h247 : (0xF7 : Word).toNat = 0xF7 := rfl
    rw [h247]
  rw [← BitVec.sub_eq_add_neg, ult_iff, hsub] at h
  have hlen_mod : (BitVec.ofNat 64 q.len).toNat = q.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt q.hlen]
  rw [hlen_mod] at h
  omega

set_option maxRecDepth 8000 in
private theorem lbb1_mem_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (rf₀ rfB0 rfC8 rfB8 rfLB rf : RegFile)
    (wsB0 wsC8 wsB8 wsLB ws : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hws : ws.length = 40 * d + 8)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrf2 : rfB8 = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).1)
    (hrf3 : rfLB = (execBlock ⟨inBase, bs⟩ fp rfB8 wsB8
      [.LI .x6 0xB8]).1)
    (hrf4 : rf = (execBlock ⟨inBase, bs⟩ fp rfLB wsLB
      [.ADDI .x7 .x5 (-0xB7)]).1)
    (hnshortb : ¬ (Cond.bltu .x5 .x6).holds rfLB)
    (hlbtr : (Cond.bltu .x7 .x11).holds rf) :
    blockVCs ⟨inBase, bs⟩ fp rf ws [.LBU .x6 .x10 1] := by
    have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    have hblen : bs.length < 2 ^ 64 := by omega
    rw [h1] at hne
    have hlen0 : 0 < len := by
      rcases Nat.eq_zero_or_pos len with h0 | hp
      · exact absurd (by rw [hx11, h0]; simp :
          rf₀.get .x11 = rf₀.get .x0) hne
      · exact hp
    have hoffb : off < bs.length := by omega
    -- engine through b0
    rw [h1] at hrf1
    rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
    -- engine through c80 / cB8 / lb (pure ALU blocks)
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      at hrf2 hrf3 hrf4
    -- register values along the path
    have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
    have hv5 : rfC8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
      rw [hrf1]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    have hv5B8 : rfB8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
      rw [hrf2]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hv5
    have hv5LB : rfLB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
      rw [hrf3]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hv5B8
    -- branch facts
    have hgeB8 : 0xB8 ≤ (bs.getD off 0).toNat := by
      have h : ¬ (BitVec.ult (rfLB.get .x5) (rfLB.get .x6) = true) := hnshortb
      rw [hv5LB, show rfLB.get .x6 = (0xB8 : Word) from by
        rw [hrf3]
        simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
          not_false_eq_true]] at h
      rw [ult_iff, toNat_zx] at h
      have h184 : ((0xB8 : Word)).toNat = 0xB8 := rfl
      omega
    have hx7 : rf.get .x7
        = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xB7) := by
      rw [hrf4]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rw [hv5LB, se12_nB7]
      bv_omega
    have hv11 : rf.get .x11 = BitVec.ofNat 64 len := by
      rw [hrf4]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hrf3]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hrf2]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hrf1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx11
    have hv10 : rf.get .x10 = inBase + BitVec.ofNat 64 off := by
      rw [hrf4]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hrf3]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hrf2]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [hrf1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx10
    have hll : (bs.getD off 0).toNat - 0xB7 < len := by
      have h : BitVec.ult (rf.get .x7) (rf.get .x11) = true := hlbtr
      rw [hx7, hv11, ult_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
      have hwfr2 : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
      omega
    have hoff1 : off + 1 < bs.length := by omega
    -- the LBU at off + 1
    have haddr : rf.get .x10 + signExtend12 (1 : BitVec 12)
        = inBase + BitVec.ofNat 64 (off + 1) := by
      rw [se12_1, hv10]
      bv_omega
    have hnorw : ¬ inRw fp ws
        (rf.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
      rw [haddr]
      exact L.not_inRw hws hoff1
    simp only [blockVCs, loadSem]
    refine ⟨?_, trivial⟩
    rw [if_neg hnorw, haddr]
    exact region_loadOk1 L.regWf hoff1

set_option maxRecDepth 8000 in
private theorem sbb1_mem_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (rf₀ rfB0 rfC8 rfB8 rfSB rfS1 rf : RegFile)
    (wsB0 wsC8 wsB8 wsSB wsS1 ws : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hws : ws.length = 40 * d + 8)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrf2 : rfB8 = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).1)
    (hnsingle : ¬ (Cond.bltu .x5 .x6).holds rfB8)
    (hrf3 : rfSB = (execBlock ⟨inBase, bs⟩ fp rfB8 wsB8
      [.LI .x6 0xB8]).1)
    (hrf4 : rfS1 = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0x80), .ADDI .x6 .x7 1]).1)
    (hsbfit : (Cond.beq .x6 .x11).holds rfS1)
    (hrf5 : rf = (execBlock ⟨inBase, bs⟩ fp rfS1 wsS1
      [.LI .x6 1]).1)
    (hsbcanon : (Cond.beq .x7 .x6).holds rf) :
    blockVCs ⟨inBase, bs⟩ fp rf ws [.LBU .x6 .x10 1, .LI .x7 0x80] := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [h1] at hrf1
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf2 hrf3 hrf4 hrf5
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5 : rfC8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf1]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5B8 : rfB8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5
  have hv5SB : rfSB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5B8
  -- ¬single gives 0x80 ≤ b0
  have hge80 : 0x80 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfB8.get .x5) (rfB8.get .x6) = true) := hnsingle
    rw [hv5B8, show rfB8.get .x6 = (0x80 : Word) from by
      rw [hrf2]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have h128 : ((0x80 : Word)).toNat = 0x80 := rfl
    omega
  -- x7 = lenRaw at rfS1 (and rf)
  have hx7S1 : rfS1.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0x80) := by
    rw [hrf4]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hv5SB, se12_n80]
    bv_omega
  -- x6 = lenRaw + 1 at rfS1
  have hx6S1 : rfS1.get .x6
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0x80) + 1 := by
    rw [hrf4]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5SB, se12_n80, se12_1]
    bv_omega
  -- x11 threaded
  have hv11S1 : rfS1.get .x11 = BitVec.ofNat 64 len := by
    rw [hrf4]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  -- sbfit: len = lenRaw + 1; sbcanon: lenRaw = 1 → len = 2
  have hfit : len = ((bs.getD off 0).toNat - 0x80) + 1 := by
    have h : rfS1.get .x6 = rfS1.get .x11 := hsbfit
    rw [hx6S1, hv11S1] at h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h1n : ((1 : Word)).toNat = 1 := rfl
    omega
  have hcanon : (bs.getD off 0).toNat - 0x80 = 1 := by
    have h : rf.get .x7 = rf.get .x6 := hsbcanon
    rw [hrf5] at h
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true] at h
    rw [hx7S1] at h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat] at this
    have h1n : ((1 : Word)).toNat = 1 := rfl
    omega
  have hoff1 : off + 1 < bs.length := by omega
  have hv10 : rf.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf5]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf4]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  have haddr : rf.get .x10 + signExtend12 (1 : BitVec 12)
      = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [se12_1, hv10]
    bv_omega
  have hnorw : ¬ inRw fp ws
      (rf.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
    rw [haddr]
    exact L.not_inRw hws hoff1
  simp only [blockVCs, loadSem, storeSem]
  refine ⟨?_, trivial, trivial⟩
  rw [if_neg hnorw, haddr]
  exact region_loadOk1 L.regWf hoff1

set_option maxRecDepth 8000 in
private theorem llb1_mem_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (rf₀ rfB0 rfBD rfLL rf : RegFile)
    (wsB0 wsBD wsLL ws : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hws : ws.length = 40 * d + 8)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfBD = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrf2 : rfLL = (execBlock ⟨inBase, bs⟩ fp rfBD wsBD
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hrf3 : rf = (execBlock ⟨inBase, bs⟩ fp rfLL wsLL
      [.ADDI .x7 .x5 (-0xF7)]).1)
    (hnlistd : ¬ (Cond.bltu .x5 .x6).holds rfLL)
    (hlltr : (Cond.bltu .x7 .x11).holds rf) :
    blockVCs ⟨inBase, bs⟩ fp rf ws [.LBU .x6 .x10 1] := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [h1] at hrf1
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf2 hrf3
  have hv5 : rfBD.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf1]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5LL : rfLL.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5
  have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfLL.get .x5) (rfLL.get .x6) = true) := hnlistd
    rw [hv5LL, show rfLL.get .x6 = (0xF8 : Word) from by
      rw [hrf2]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have h248 : ((0xF8 : Word)).toNat = 0xF8 := rfl
    omega
  have hx7 : rf.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) := by
    rw [hrf3]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5LL, se12_nF7]
    have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
    bv_omega
  have hv11 : rf.get .x11 = BitVec.ofNat 64 len := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hv10 : rf.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  have hll : (bs.getD off 0).toNat - 0xF7 < len := by
    have h : BitVec.ult (rf.get .x7) (rf.get .x11) = true := hlltr
    rw [hx7, hv11, ult_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
    omega
  have hoff1 : off + 1 < bs.length := by omega
  have haddr : rf.get .x10 + signExtend12 (1 : BitVec 12)
      = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [se12_1, hv10]
    bv_omega
  have hnorw : ¬ inRw fp ws
      (rf.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
    rw [haddr]
    exact L.not_inRw hws hoff1
  simp only [blockVCs, loadSem]
  refine ⟨?_, trivial⟩
  rw [if_neg hnorw, haddr]
  exact region_loadOk1 L.regWf hoff1

/-- Register threading past the second-byte `LBU`. -/
private theorem thread_lbu1 (reg : Region) (rwBase : Word) (rfX : RegFile)
    (wsX : List (BitVec 8)) (r : Reg) (hr : r ≠ .x6) :
    ((execBlock reg rwBase rfX wsX [.LBU .x6 .x10 1]).1).get r
      = rfX.get r := by
  simp only [execBlock_cons, execBlock_nil]
  exact execInstrRF_get_ne _ _ _ _ _ _ (fun op hop => by cases hop)
    (fun l hl => by cases hl; exact hr)

set_option maxRecDepth 8000 in
private theorem lbbe_pre_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (rf₀ rfB0 rfC8 rfB8 rfLB rfLB2 rfB1 rf
      : RegFile)
    (wsB0 wsC8 wsB8 wsLB wsLB2 wsB1 ws : List (BitVec 8))
    (beS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (_hbeE : beS.entry = rdbeEntry)
    (hbePre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
        (j n : Nat), rf.get .x29 = inBase + BitVec.ofNat 64 j →
        rf.get .x30 = BitVec.ofNat 64 n → n ≤ 8 → j + n ≤ bs.length →
        beS.pre rf ws A)
    (A : Assertion)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hdisp : (Cond.bltu .x5 .x6).holds rfC8)
    (hrf2 : rfB8 = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).1)
    (hrf3 : rfLB = (execBlock ⟨inBase, bs⟩ fp rfB8 wsB8
      [.LI .x6 0xB8]).1)
    (hnshortb : ¬ (Cond.bltu .x5 .x6).holds rfLB)
    (hrf4 : rfLB2 = (execBlock ⟨inBase, bs⟩ fp rfLB wsLB
      [.ADDI .x7 .x5 (-0xB7)]).1)
    (hlbtr : (Cond.bltu .x7 .x11).holds rfLB2)
    (hrf5 : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfLB2 wsLB2
      [.LBU .x6 .x10 1]).1)
    (hrf6 : rf = (execBlock ⟨inBase, bs⟩ fp rfB1 wsB1
      [.ADDI .x29 .x10 1, .MV .x30 .x7]).1) :
    beS.pre rf ws A := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [h1] at hrf1
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf2 hrf3 hrf4 hrf6
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5 : rfC8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf1]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5B8 : rfB8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5
  have hv5LB : rfLB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5B8
  -- disp: b0 < 0xC0; ¬shortb: 0xB8 ≤ b0
  have hltC0 : (bs.getD off 0).toNat < 0xC0 := by
    have h : BitVec.ult (rfC8.get .x5) (rfC8.get .x6) = true := hdisp
    rw [hv5, show rfC8.get .x6 = (0xC0 : Word) from by
      rw [hrf1]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have hc : ((0xC0 : Word)).toNat = 0xC0 := rfl
    omega
  have hgeB8 : 0xB8 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfLB.get .x5) (rfLB.get .x6) = true) := hnshortb
    rw [hv5LB, show rfLB.get .x6 = (0xB8 : Word) from by
      rw [hrf3]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have h184 : ((0xB8 : Word)).toNat = 0xB8 := rfl
    omega
  -- x7 = ll at rfLB2, x11 and x10 threaded
  have hx7 : rfLB2.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xB7) := by
    rw [hrf4]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5LB, se12_nB7]
    bv_omega
  have hv11 : rfLB2.get .x11 = BitVec.ofNat 64 len := by
    rw [hrf4]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hv10 : rfLB2.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf4]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  have hll : (bs.getD off 0).toNat - 0xB7 < len := by
    have h : BitVec.ult (rfLB2.get .x7) (rfLB2.get .x11) = true := hlbtr
    rw [hx7, hv11, ult_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
    omega
  -- thread past the LBU
  have hv10B1 : rfB1.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf5, thread_lbu1 _ _ _ _ _ (by decide)]
    exact hv10
  have hv7B1 : rfB1.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xB7) := by
    rw [hrf5, thread_lbu1 _ _ _ _ _ (by decide)]
    exact hx7
  -- final register values
  have hx29 : rf.get .x29 = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [hrf6]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hv10B1, se12_1]
    bv_omega
  have hx30 : rf.get .x30
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xB7) := by
    rw [hrf6]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    exact hv7B1
  exact hbePre rf ws A (off + 1) ((bs.getD off 0).toNat - 0xB7)
    hx29 hx30 (by omega) (by omega)

set_option maxRecDepth 8000 in
private theorem llbe_pre_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (rf₀ rfB0 rfBD rfLL rfLL2 rfB1 rf : RegFile)
    (wsB0 wsBD wsLL wsLL2 wsB1 ws : List (BitVec 8))
    (beS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (_hbeE : beS.entry = rdbeEntry)
    (hbePre : ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
        (j n : Nat), rf.get .x29 = inBase + BitVec.ofNat 64 j →
        rf.get .x30 = BitVec.ofNat 64 n → n ≤ 8 → j + n ≤ bs.length →
        beS.pre rf ws A)
    (A : Assertion)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfBD = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrf2 : rfLL = (execBlock ⟨inBase, bs⟩ fp rfBD wsBD
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hnlistd : ¬ (Cond.bltu .x5 .x6).holds rfLL)
    (hrf3 : rfLL2 = (execBlock ⟨inBase, bs⟩ fp rfLL wsLL
      [.ADDI .x7 .x5 (-0xF7)]).1)
    (hlltr : (Cond.bltu .x7 .x11).holds rfLL2)
    (hrf4 : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfLL2 wsLL2
      [.LBU .x6 .x10 1]).1)
    (hrf5 : rf = (execBlock ⟨inBase, bs⟩ fp rfB1 wsB1
      [.ADDI .x29 .x10 1, .MV .x30 .x7]).1) :
    beS.pre rf ws A := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [h1] at hrf1
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf2 hrf3 hrf5
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5 : rfBD.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf1]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5LL : rfLL.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5
  have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfLL.get .x5) (rfLL.get .x6) = true) := hnlistd
    rw [hv5LL, show rfLL.get .x6 = (0xF8 : Word) from by
      rw [hrf2]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have h248 : ((0xF8 : Word)).toNat = 0xF8 := rfl
    omega
  have hx7 : rfLL2.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) := by
    rw [hrf3]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5LL, se12_nF7]
    bv_omega
  have hv11 : rfLL2.get .x11 = BitVec.ofNat 64 len := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hv10 : rfLL2.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  have hll : (bs.getD off 0).toNat - 0xF7 < len := by
    have h : BitVec.ult (rfLL2.get .x7) (rfLL2.get .x11) = true := hlltr
    rw [hx7, hv11, ult_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
    omega
  have hv10B1 : rfB1.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf4, thread_lbu1 _ _ _ _ _ (by decide)]
    exact hv10
  have hv7B1 : rfB1.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) := by
    rw [hrf4, thread_lbu1 _ _ _ _ _ (by decide)]
    exact hx7
  have hx29 : rf.get .x29 = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [hrf5]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hv10B1, se12_1]
    bv_omega
  have hx30 : rf.get .x30
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) := by
    rw [hrf5]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    exact hv7B1
  exact hbePre rf ws A (off + 1) ((bs.getD off 0).toNat - 0xF7)
    hx29 hx30 (by omega) (by omega)

set_option maxRecDepth 8000 in
private theorem items_pre_short_core (bs : List Byte) (inBase : Word)
    (d : Nat) (fp : Word) (off len : Nat)
    (rf₀ rfB0 rfBD rfSL rfG rf : RegFile)
    (wsB0 wsBD wsSL wsG ws : List (BitVec 8))
    (itemsS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (hd64 : d < 2 ^ 64)
    (_hitE : itemsS.entry = itemsEntry)
    (hitPre : 1 ≤ d → ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsPreS bs inBase (d - 1) (fp + 8) rf ws A → itemsS.pre rf ws A)
    (A : Assertion)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfBD = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hndisp : ¬ (Cond.bltu .x5 .x6).holds rfBD)
    (hnbud : ¬ (Cond.beq .x12 .x0).holds rfBD)
    (hrf2 : rfSL = (execBlock ⟨inBase, bs⟩ fp rfBD wsBD
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hrf3 : rfG = (execBlock ⟨inBase, bs⟩ fp rfSL wsSL
      [.ADDI .x7 .x5 (-0xC0), .ADDI .x6 .x7 1]).1)
    (hslfit : (Cond.beq .x6 .x11).holds rfG)
    (hrf4 : rf = (execBlock ⟨inBase, bs⟩ fp
      (execBlock ⟨inBase, bs⟩ fp rfG wsG
        [.ADDI .x15 .x10 1, .ADD .x16 .x15 .x7, .LI .x14 0]).1 wsG
      [.ADDI .x13 .x13 8]).1) :
    itemsS.pre rf ws A := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [h1] at hrf1
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf2 hrf3 hrf4
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5 : rfBD.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf1]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  -- ¬disp: 0xC0 ≤ b0
  have hgeC0 : 0xC0 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfBD.get .x5) (rfBD.get .x6) = true) := hndisp
    rw [hv5, show rfBD.get .x6 = (0xC0 : Word) from by
      rw [hrf1]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have hc : ((0xC0 : Word)).toNat = 0xC0 := rfl
    omega
  -- ¬bud: d ≥ 1
  have hd1 : 1 ≤ d := by
    have h : rfBD.get .x12 ≠ rfBD.get .x0 := hnbud
    have h12 : rfBD.get .x12 = BitVec.ofNat 64 d := by
      rw [hrf1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx12
    rcases Nat.eq_zero_or_pos d with h0 | hp
    · exact absurd (by rw [h12, h0]; simp : rfBD.get .x12 = rfBD.get .x0) h
    · exact hp
  -- register values through budm / sl
  have hv5SL : rfSL.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5
  have hx7G : rfG.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xC0) := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hv5SL, se12_nC0]
    bv_omega
  have hx6G : rfG.get .x6
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xC0) + 1 := by
    rw [hrf3]
    simp only [RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hv5SL, se12_nC0, se12_1]
    bv_omega
  have hx11G : rfG.get .x11 = BitVec.ofNat 64 len := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hx10G : rfG.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  have hx12G : rfG.get .x12 = BitVec.ofNat 64 (d - 1) := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx12, se12_n1]
    bv_omega
  have hx13G : rfG.get .x13 = fp := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx13
  -- slfit: len = payLen + 1
  have hfit : len = ((bs.getD off 0).toNat - 0xC0) + 1 := by
    have h : rfG.get .x6 = rfG.get .x11 := hslfit
    rw [hx6G, hx11G] at h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h1n : ((1 : Word)).toNat = 1 := rfl
    omega
  -- final registers
  apply hitPre hd1 rf ws A
  refine ⟨off + 1, off + len, ?_, ?_, ?_, ?_, by omega, by omega⟩
  · rw [hrf4]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hx10G, se12_1]
    bv_omega
  · rw [hrf4]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hx10G, hx7G, se12_1]
    have hlt : off + len ≤ bs.length := hoff
    bv_omega
  · rw [hrf4]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12G
  · rw [hrf4]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hx13G, se12_8]

private theorem idxOf_add (inBase : Word) (j : Nat) (hb : j < 2 ^ 64)
    (hnw : inBase.toNat + j < 2 ^ 64) :
    idxOf inBase (inBase + BitVec.ofNat 64 j) = j := by
  unfold idxOf
  have haddr : (inBase + BitVec.ofNat 64 j).toNat = inBase.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.toNat_sub, haddr]
  omega

set_option maxRecDepth 8000 in
private theorem items_pre_long_core (bs : List Byte) (inBase : Word)
    (d : Nat) (fp : Word) (off len : Nat)
    (rf₀ rfB0 rfBD rfLL rfLL2 rfB1 rf₁ rfP rfC38 rfF rfG rf : RegFile)
    (wsB0 wsBD wsLL wsLL2 wsB1 ws₁ wsP wsC38 wsF wsG ws : List (BitVec 8))
    (A₁ AP : Assertion)
    (beS itemsS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (hd64 : d < 2 ^ 64)
    (_hitE : itemsS.entry = itemsEntry)
    (hitPre : 1 ≤ d → ∀ (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsPreS bs inBase (d - 1) (fp + 8) rf ws A → itemsS.pre rf ws A)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (A : Assertion)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrf1 : rfBD = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hnbud : ¬ (Cond.beq .x12 .x0).holds rfBD)
    (hrf2 : rfLL = (execBlock ⟨inBase, bs⟩ fp rfBD wsBD
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hnlistd : ¬ (Cond.bltu .x5 .x6).holds rfLL)
    (hrf3 : rfLL2 = (execBlock ⟨inBase, bs⟩ fp rfLL wsLL
      [.ADDI .x7 .x5 (-0xF7)]).1)
    (hlltr : (Cond.bltu .x7 .x11).holds rfLL2)
    (hrf4 : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfLL2 wsLL2
      [.LBU .x6 .x10 1]).1)
    (hrf5 : rf₁ = (execBlock ⟨inBase, bs⟩ fp rfB1 wsB1
      [.ADDI .x29 .x10 1, .MV .x30 .x7]).1)
    (hpost : beS.post rf₁ ws₁ A₁ rfP wsP AP)
    (hrf6 : rfC38 = (execBlock ⟨inBase, bs⟩ fp rfP wsP
      [.LI .x6 0x38]).1)
    (_hnsmall : ¬ (Cond.bltu .x31 .x6).holds rfC38)
    (hrf7 : rfF = (execBlock ⟨inBase, bs⟩ fp rfC38 wsC38
      [.ADDI .x6 .x11 (-1), .SUB .x6 .x6 .x7]).1)
    (hllfit2 : (Cond.beq .x31 .x6).holds rfF)
    (hrf8 : rfG = (execBlock ⟨inBase, bs⟩ fp rfF wsF
      [.ADDI .x15 .x10 1, .ADD .x15 .x15 .x7, .ADD .x16 .x15 .x31,
       .LI .x14 0]).1)
    (hrf9 : rf = (execBlock ⟨inBase, bs⟩ fp rfG wsG
      [.ADDI .x13 .x13 8]).1) :
    itemsS.pre rf ws A := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [h1] at hrf1
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrf1
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf2 hrf3 hrf5 hrf6 hrf7 hrf8 hrf9
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5 : rfBD.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf1]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hd1 : 1 ≤ d := by
    have h : rfBD.get .x12 ≠ rfBD.get .x0 := hnbud
    have h12 : rfBD.get .x12 = BitVec.ofNat 64 d := by
      rw [hrf1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx12
    rcases Nat.eq_zero_or_pos d with h0 | hp
    · exact absurd (by rw [h12, h0]; simp : rfBD.get .x12 = rfBD.get .x0) h
    · exact hp
  have hv5LL : rfLL.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5
  have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfLL.get .x5) (rfLL.get .x6) = true) := hnlistd
    rw [hv5LL, show rfLL.get .x6 = (0xF8 : Word) from by
      rw [hrf2]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have h248 : ((0xF8 : Word)).toNat = 0xF8 := rfl
    omega
  have hx7LL2 : rfLL2.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) := by
    rw [hrf3]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5LL, se12_nF7]
    bv_omega
  have hv11LL2 : rfLL2.get .x11 = BitVec.ofNat 64 len := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hv10LL2 : rfLL2.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  have hv12LL2 : rfLL2.get .x12 = BitVec.ofNat 64 (d - 1) := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx12, se12_n1]
    bv_omega
  have hv13LL2 : rfLL2.get .x13 = fp := by
    rw [hrf3]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf2]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx13
  have hll : (bs.getD off 0).toNat - 0xF7 < len := by
    have h : BitVec.ult (rfLL2.get .x7) (rfLL2.get .x11) = true := hlltr
    rw [hx7LL2, hv11LL2, ult_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
    omega
  -- thread past the second-byte LBU
  have hT : ∀ (r : Reg), r ≠ .x6 → rfB1.get r = rfLL2.get r := by
    intro r hr
    rw [hrf4]
    exact thread_lbu1 _ _ _ _ _ hr
  -- registers at the leaf call's entry state
  have hx29r1 : rf₁.get .x29 = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [hrf5]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hT .x10 (by decide), hv10LL2, se12_1]
    bv_omega
  have hx30r1 : rf₁.get .x30
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) := by
    rw [hrf5]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hT .x7 (by decide), hx7LL2]
  -- the leaf's post: x31 = the BE value; the rest pinned
  obtain ⟨hx31P, hpins, hwsP, hAP⟩ := hbePost rf₁ ws₁ A₁ rfP wsP AP hpost
  set ll := (bs.getD off 0).toNat - 0xF7 with hlldef
  have hll8 : ll ≤ 8 := by
    rw [hlldef]
    omega
  have hbeV : rfP.get .x31 = BitVec.ofNat 64 (beVal bs (off + 1) ll) := by
    rw [hx31P, hx29r1, hx30r1]
    rw [idxOf_add inBase (off + 1) (by omega) (by omega),
      BitVec.toNat_ofNat]
    congr 2
    omega
  have hbeLt : beVal bs (off + 1) ll < 2 ^ 64 := by
    unfold beVal
    have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt ((bs.drop (off + 1)).take ll)
    have hlen : ((bs.drop (off + 1)).take ll).length ≤ ll := by
      rw [List.length_take]
      omega
    calc EvmAsm.EL.RLP.Nat.fromBytesBE ((bs.drop (off + 1)).take ll)
        < 256 ^ ((bs.drop (off + 1)).take ll).length := h
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  -- pins through to rfP
  have hx10P : rfP.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hpins .x10 (by decide) (by decide) (by decide) (by decide), hrf5]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hT .x10 (by decide)]
    exact hv10LL2
  have hx11P : rfP.get .x11 = BitVec.ofNat 64 len := by
    rw [hpins .x11 (by decide) (by decide) (by decide) (by decide), hrf5]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hT .x11 (by decide)]
    exact hv11LL2
  have hx12P : rfP.get .x12 = BitVec.ofNat 64 (d - 1) := by
    rw [hpins .x12 (by decide) (by decide) (by decide) (by decide), hrf5]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hT .x12 (by decide)]
    exact hv12LL2
  have hx13P : rfP.get .x13 = fp := by
    rw [hpins .x13 (by decide) (by decide) (by decide) (by decide), hrf5]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hT .x13 (by decide)]
    exact hv13LL2
  have hx7P : rfP.get .x7 = BitVec.ofNat 64 ll := by
    rw [hpins .x7 (by decide) (by decide) (by decide) (by decide), hrf5]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hT .x7 (by decide)]
    exact hx7LL2
  -- llfit2: beVal = len - 1 - ll
  have hx6F : rfF.get .x6 = BitVec.ofNat 64 (len - 1 - ll) := by
    rw [hrf7]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ Reg.x6)]
    rw [show rfC38.get .x11 = BitVec.ofNat 64 len from by
        rw [hrf6]
        simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        exact hx11P,
      show rfC38.get .x7 = BitVec.ofNat 64 ll from by
        rw [hrf6]
        simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        exact hx7P,
      se12_n1]
    bv_omega
  have hx31F : rfF.get .x31 = BitVec.ofNat 64 (beVal bs (off + 1) ll) := by
    rw [hrf7]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf6]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hbeV
  have hval : beVal bs (off + 1) ll = len - 1 - ll := by
    have h : rfF.get .x31 = rfF.get .x6 := hllfit2
    rw [hx31F, hx6F] at h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    omega
  -- registers at rfG (llgo) and rf (goitems)
  have hx10F : rfF.get .x10 = inBase + BitVec.ofNat 64 off := by
    rw [hrf7]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf6]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10P
  have hx7F : rfF.get .x7 = BitVec.ofNat 64 ll := by
    rw [hrf7]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf6]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx7P
  have hx12F : rfF.get .x12 = BitVec.ofNat 64 (d - 1) := by
    rw [hrf7]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf6]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12P
  have hx13F : rfF.get .x13 = fp := by
    rw [hrf7]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf6]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx13P
  apply hitPre hd1 rf ws A
  refine ⟨off + 1 + ll, off + len, ?_, ?_, ?_, ?_, by omega, by omega⟩
  · rw [hrf9]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf8]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hx10F, hx7F, se12_1]
    bv_omega
  · rw [hrf9]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf8]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hx10F, hx7F, hx31F, hval, se12_1]
    have hlt : off + len ≤ bs.length := hoff
    bv_omega
  · rw [hrf9]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrf8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx12F
  · rw [hrf9]
    simp only [RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hrf8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hx13F, se12_8]

set_option maxRecDepth 8000 in
/-- Shared facts at the post-`sb1` state of the short-byte-string fit
    path. -/
private theorem short_fit_facts (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8))
    (rfB0 rfC8 rfCB rfSB rfS1 rfQ : RegFile)
    (wsB0 wsC8 wsCB wsSB wsS1 wsQ : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx13 : rf₀.get .x13 = fp)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (h2 : wsB0 = setBytes ws₀ 0 (dwordBytes v))
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrfB0 : rfC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrfC8 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).1)
    (hnsingle : ¬ (Cond.bltu .x5 .x6).holds rfCB)
    (hrfCB : rfSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.LI .x6 0xB8]).1)
    (hshortb : (Cond.bltu .x5 .x6).holds rfSB)
    (hrfSB : rfS1 = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0x80), .ADDI .x6 .x7 1]).1)
    (hsbfit : (Cond.beq .x6 .x11).holds rfS1)
    (hrfS1 : rfQ = (execBlock ⟨inBase, bs⟩ fp rfS1 wsS1
      [.LI .x6 1]).1)
    (hwsB0 : wsC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).2)
    (hwsC8 : wsCB = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).2)
    (hwsCB : wsSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.LI .x6 0xB8]).2)
    (hwsSB : wsS1 = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0x80), .ADDI .x6 .x7 1]).2)
    (hwsS1 : wsQ = (execBlock ⟨inBase, bs⟩ fp rfS1 wsS1
      [.LI .x6 1]).2) :
    0x80 ≤ (bs.getD off 0).toNat
    ∧ (bs.getD off 0).toNat ≤ 0xB7
    ∧ len = 1 + ((bs.getD off 0).toNat - 0x80)
    ∧ rfQ.get .x10 = inBase + BitVec.ofNat 64 off
    ∧ rfQ.get .x13 = fp
    ∧ rfQ.get .x7 = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0x80)
    ∧ wsQ.take 8 = dwordBytes v
    ∧ wsQ = setBytes ws₀ 0 (dwordBytes v) := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne hrfB0
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrfB0
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrfC8 hrfCB hrfSB hrfS1
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5C8 : rfC8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfB0]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5CB : rfCB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5C8
  have hv5SB : rfSB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5CB
  have hge80 : 0x80 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfCB.get .x5) (rfCB.get .x6) = true) := hnsingle
    rw [hv5CB, show rfCB.get .x6 = (0x80 : Word) from by
      rw [hrfC8]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have hc : ((0x80 : Word)).toNat = 0x80 := rfl
    omega
  have hleB7 : (bs.getD off 0).toNat ≤ 0xB7 := by
    have h : BitVec.ult (rfSB.get .x5) (rfSB.get .x6) = true := hshortb
    rw [hv5SB, show rfSB.get .x6 = (0xB8 : Word) from by
      rw [hrfCB]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have hc : ((0xB8 : Word)).toNat = 0xB8 := rfl
    omega
  have hx7S1 : rfS1.get .x7
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0x80) := by
    rw [hrfSB]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hv5SB, se12_n80]
    bv_omega
  have hx6S1 : rfS1.get .x6
      = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0x80) + 1 := by
    rw [hrfSB]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5SB, se12_n80, se12_1]
    bv_omega
  have hx11S1 : rfS1.get .x11 = BitVec.ofNat 64 len := by
    rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  have hfit : len = 1 + ((bs.getD off 0).toNat - 0x80) := by
    have h : rfS1.get .x6 = rfS1.get .x11 := hsbfit
    rw [hx6S1, hx11S1] at h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have h1n : ((1 : Word)).toNat = 1 := rfl
    omega
  have hwq : wsQ = setBytes ws₀ 0 (dwordBytes v) := by
    have e1 : wsQ = wsS1 := hwsS1
    have e2 : wsS1 = wsSB := hwsSB
    have e3 : wsSB = wsCB := hwsCB
    have e4 : wsCB = wsC8 := hwsC8
    have e5 : wsC8 = wsB0 := hwsB0
    rw [e1, e2, e3, e4, e5, h2]
  refine ⟨hge80, hleB7, hfit, ?_, ?_, ?_, ?_, hwq⟩
  · rw [hrfS1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrfS1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx13
  · rw [hrfS1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx7S1
  · rw [hwq]
    have hs := setBytes_slot ws₀ (dwordBytes v) 0
      (by
        rw [length_dwordBytes]
        have hl : wsB0.length = 40 * d + 8 := hlenB0
        rw [h2, length_setBytes] at hl
        omega)
    rw [List.drop_zero, length_dwordBytes] at hs
    exact hs

set_option maxRecDepth 8000 in
/-- Shared facts at the post-`lb` state of the long-byte-string path. -/
private theorem long_stem_facts (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8))
    (rfB0 rfC8 rfCB rfSB rfQ : RegFile)
    (wsB0 wsC8 wsCB wsSB wsQ : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx13 : rf₀.get .x13 = fp)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (h1 : rfB0 = rf₀)
    (h2 : wsB0 = setBytes ws₀ 0 (dwordBytes v))
    (hne : ¬ (Cond.beq .x11 .x0).holds rfB0)
    (hrfB0 : rfC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hdisp : (Cond.bltu .x5 .x6).holds rfC8)
    (hrfC8 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).1)
    (_hnsingle : ¬ (Cond.bltu .x5 .x6).holds rfCB)
    (hrfCB : rfSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.LI .x6 0xB8]).1)
    (hnshortb : ¬ (Cond.bltu .x5 .x6).holds rfSB)
    (hrfSB : rfQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0xB7)]).1)
    (hwsB0 : wsC8 = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).2)
    (hwsC8 : wsCB = (execBlock ⟨inBase, bs⟩ fp rfC8 wsC8
      [.LI .x6 0x80]).2)
    (hwsCB : wsSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.LI .x6 0xB8]).2)
    (hwsSB : wsQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0xB7)]).2) :
    0xB8 ≤ (bs.getD off 0).toNat
    ∧ (bs.getD off 0).toNat ≤ 0xBF
    ∧ 0 < len
    ∧ rfQ.get .x10 = inBase + BitVec.ofNat 64 off
    ∧ rfQ.get .x11 = BitVec.ofNat 64 len
    ∧ rfQ.get .x13 = fp
    ∧ rfQ.get .x7 = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xB7)
    ∧ wsQ.take 8 = dwordBytes v
    ∧ wsQ = setBytes ws₀ 0 (dwordBytes v) := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hne hrfB0
  have hlen0 : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h0 | hp
    · exact absurd (by rw [hx11, h0]; simp :
        rf₀.get .x11 = rf₀.get .x0) hne
    · exact hp
  have hoffb : off < bs.length := by omega
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb] at hrfB0
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrfC8 hrfCB hrfSB
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  have hv5C8 : rfC8.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfB0]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5CB : rfCB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5C8
  have hv5SB : rfSB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hv5CB
  have hleBF : (bs.getD off 0).toNat ≤ 0xBF := by
    have h : BitVec.ult (rfC8.get .x5) (rfC8.get .x6) = true := hdisp
    rw [hv5C8, show rfC8.get .x6 = (0xC0 : Word) from by
      rw [hrfB0]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have hc : ((0xC0 : Word)).toNat = 0xC0 := rfl
    omega
  have hgeB8 : 0xB8 ≤ (bs.getD off 0).toNat := by
    have h : ¬ (BitVec.ult (rfSB.get .x5) (rfSB.get .x6) = true) := hnshortb
    rw [hv5SB, show rfSB.get .x6 = (0xB8 : Word) from by
      rw [hrfCB]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]] at h
    rw [ult_iff, toNat_zx] at h
    have hc : ((0xB8 : Word)).toNat = 0xB8 := rfl
    omega
  have hwq : wsQ = setBytes ws₀ 0 (dwordBytes v) := by
    have e1 : wsQ = wsSB := hwsSB
    have e2 : wsSB = wsCB := hwsCB
    have e3 : wsCB = wsC8 := hwsC8
    have e4 : wsC8 = wsB0 := hwsB0
    rw [e1, e2, e3, e4, h2]
  refine ⟨hgeB8, hleBF, hlen0, ?_, ?_, ?_, ?_, ?_, hwq⟩
  · rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  · rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfC8]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx13
  · rw [hrfSB]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5SB, se12_nB7]
    bv_omega
  · rw [hwq]
    have hs := setBytes_slot ws₀ (dwordBytes v) 0
      (by
        rw [length_dwordBytes]
        have hl : wsB0.length = 40 * d + 8 := hlenB0
        rw [h2, length_setBytes] at hl
        omega)
    rw [List.drop_zero, length_dwordBytes] at hs
    exact hs

set_option maxRecDepth 8000 in
/-- Register and writable-state facts through the `-0xF7` long-list stem.
    This deliberately stops before the second-byte load and is shared by the
    small and bad-length no-go arms. -/
private theorem long_prefix_f7_facts (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8)) (rfB0 rfCB rfSB rfQ : RegFile)
    (wsB0 wsCB wsSB wsQ : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx13 : rf₀.get .x13 = fp)
    (hlenB0 : wsB0.length = 40 * d + 8)
    (hlen0 : 0 < len)
    (hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat)
    (h1 : rfB0 = rf₀)
    (h2 : wsB0 = setBytes ws₀ 0 (dwordBytes v))
    (hrfB0 : rfCB = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).1)
    (hrfCB : rfSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1)
    (hrfSB : rfQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0xF7)]).1)
    (hwsB0 : wsCB = (execBlock ⟨inBase, bs⟩ fp rfB0 wsB0
      [.LBU .x5 .x10 0, .LI .x6 0xC0]).2)
    (hwsCB : wsSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
      [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).2)
    (hwsSB : wsQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
      [.ADDI .x7 .x5 (-0xF7)]).2) :
    rfQ.get .x10 = inBase + BitVec.ofNat 64 off
    ∧ rfQ.get .x11 = BitVec.ofNat 64 len
    ∧ rfQ.get .x13 = fp
    ∧ rfQ.get .x7 = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7)
    ∧ wsQ.take 8 = dwordBytes v
    ∧ wsQ = setBytes ws₀ 0 (dwordBytes v) := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  rw [h1] at hrfB0
  have hoffb : off < bs.length := by omega
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb]
    at hrfB0
  rw [h1] at hwsB0
  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb]
    at hwsB0
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrfCB hrfSB hwsCB hwsSB
  have hv5CB : rfCB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfB0]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
  have hv5SB : rfSB.get .x5 = (bs.getD off 0).zeroExtend 64 := by
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
      not_false_eq_true]
    exact hv5CB
  have hwq : wsQ = setBytes ws₀ 0 (dwordBytes v) := by
    rw [hwsSB, hwsCB, hwsB0, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, hwq⟩
  · rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx10
  · rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx11
  · rw [hrfSB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfCB]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hrfB0]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx13
  · rw [hrfSB]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hv5SB, se12_nF7]
    bv_omega
  · have hs := setBytes_slot ws₀ (dwordBytes v) 0
      (by
        rw [length_dwordBytes]
        have hl : wsB0.length = 40 * d + 8 := hlenB0
        rw [h2, length_setBytes] at hl
        omega)
    rw [List.drop_zero, length_dwordBytes] at hs
    rw [hwq]
    exact hs

set_option maxRecDepth 8000 in
/-- Facts at the post-`lbc` state of the long-byte-string call path:
    the second byte is nonzero, `x31` holds the BE length value, the
    argument registers are pinned. -/
private theorem long_call_facts (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (_rf₀ : RegFile)
    (rfQ rfB1 rf₁ rfP rfY : RegFile)
    (wsQ wsB1 ws₁ wsP wsY : List (BitVec 8))
    (A₁ AP : Assertion)
    (beS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (k : Nat)
    (hll1 : 1 ≤ (bs.getD off 0).toNat - k)
    (hll8 : (bs.getD off 0).toNat - k ≤ 8)
    (hll : (bs.getD off 0).toNat - k < len)
    (hx10Q : rfQ.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11Q : rfQ.get .x11 = BitVec.ofNat 64 len)
    (hx13Q : rfQ.get .x13 = fp)
    (hx7Q : rfQ.get .x7 = BitVec.ofNat 64 ((bs.getD off 0).toNat - k))
    (hlenQ : wsQ.length = 40 * d + 8)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (hrfB1 : rfB1 = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
      [.LBU .x6 .x10 1]).1)
    (hnlbz : ¬ (Cond.beq .x6 .x0).holds rfB1)
    (hrf₁ : rf₁ = (execBlock ⟨inBase, bs⟩ fp rfB1 wsB1
      [.ADDI .x29 .x10 1, .MV .x30 .x7]).1)
    (hpost : beS.post rf₁ ws₁ A₁ rfP wsP AP)
    (hrfY : rfY = (execBlock ⟨inBase, bs⟩ fp rfP wsP
      [.LI .x6 0x38]).1)
    (hwsQ2 : wsB1 = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
      [.LBU .x6 .x10 1]).2)
    (hwsB1 : ws₁ = (execBlock ⟨inBase, bs⟩ fp rfB1 wsB1
      [.ADDI .x29 .x10 1, .MV .x30 .x7]).2)
    (hwsP : wsY = (execBlock ⟨inBase, bs⟩ fp rfP wsP
      [.LI .x6 0x38]).2) :
    bs.getD (off + 1) 0 ≠ 0
    ∧ rfY.get .x31 = BitVec.ofNat 64
        (beVal bs (off + 1) ((bs.getD off 0).toNat - k))
    ∧ beVal bs (off + 1) ((bs.getD off 0).toNat - k) < 2 ^ 64
    ∧ rfY.get .x11 = BitVec.ofNat 64 len
    ∧ rfY.get .x13 = fp
    ∧ rfY.get .x7 = BitVec.ofNat 64 ((bs.getD off 0).toNat - k)
    ∧ rfY.get .x6 = (0x38 : Word)
    ∧ wsY = wsQ := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
  set ll := (bs.getD off 0).toNat - k with hlldef
  have hll1ll : 1 ≤ ll := by rw [hlldef]; exact hll1
  have hll8ll : ll ≤ 8 := by rw [hlldef]; exact hll8
  have hoff1 : off + 1 < bs.length := by omega
  -- resolve the second-byte load
  have haddr1 : rfQ.get .x10 + signExtend12 (1 : BitVec 12)
      = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [se12_1, hx10Q]
    bv_omega
  have hnorw1 : ¬ inRw fp wsQ
      (rfQ.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
    rw [haddr1]
    exact L.not_inRw hlenQ hoff1
  have hstep : (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
      [.LBU .x6 .x10 1]).1
    = rfQ.set .x6 ((bs.getD (off + 1) 0).zeroExtend 64) := by
    simp only [execBlock_cons, execBlock_nil]
    rw [lbu_ro _ _ _ _ _ _ _ hnorw1, haddr1, region_byteAt L.regWf hoff1]
  rw [hstep] at hrfB1
  -- b1 nonzero from the ¬lbz branch
  have hb1ne : bs.getD (off + 1) 0 ≠ 0 := by
    intro hcontra
    apply hnlbz
    show rfB1.get .x6 = rfB1.get .x0
    rw [hrfB1]
    simp only [RegFile.get_set_self, RegFile.get_x0, ne_eq, reduceCtorEq,
      not_false_eq_true]
    rw [hcontra]
    rfl
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    at hrf₁ hrfY
  -- entry registers of the leaf call
  have hx29r1 : rf₁.get .x29 = inBase + BitVec.ofNat 64 (off + 1) := by
    rw [hrf₁]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [show rfB1.get .x10 = inBase + BitVec.ofNat 64 off from by
        rw [hrfB1]
        simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        exact hx10Q, se12_1]
    bv_omega
  have hx30r1 : rf₁.get .x30 = BitVec.ofNat 64 ll := by
    rw [hrf₁]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [hrfB1]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hx7Q
  obtain ⟨hx31P, hpins, hwsPeq, hAP⟩ := hbePost rf₁ ws₁ A₁ rfP wsP AP hpost
  have hbeV : rfP.get .x31 = BitVec.ofNat 64 (beVal bs (off + 1) ll) := by
    rw [hx31P, hx29r1, hx30r1,
      idxOf_add inBase (off + 1) (by omega) (by omega), BitVec.toNat_ofNat]
    congr 2
    omega
  have hbeLt : beVal bs (off + 1) ll < 2 ^ 64 := by
    unfold beVal
    have h := EvmAsm.EL.RLP.Nat.fromBytesBE_lt ((bs.drop (off + 1)).take ll)
    have hlen : ((bs.drop (off + 1)).take ll).length ≤ ll := by
      rw [List.length_take]
      omega
    have htake8 : ((bs.drop (off + 1)).take ll).length ≤ 8 :=
      le_trans hlen hll8ll
    calc EvmAsm.EL.RLP.Nat.fromBytesBE ((bs.drop (off + 1)).take ll)
        < 256 ^ ((bs.drop (off + 1)).take ll).length := h
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) htake8
  have hpin : ∀ (r : Reg), r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
      r ≠ .x6 → rfP.get r = rfQ.get r := by
    intro r h28 h29 h30 h31 h6
    rw [hpins r h28 h29 h30 h31, hrf₁]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [RegFile.get_set_ne _ _ _ _ h30,
      RegFile.get_set_ne _ _ _ _ h29, hrfB1,
      RegFile.get_set_ne _ _ _ _ h6]
  have hwsAll : wsY = wsQ := by
    have e1 : wsY = wsP := hwsP
    have e2 : wsP = ws₁ := hwsPeq
    have e3 : ws₁ = wsB1 := hwsB1
    have e4 : wsB1 = wsQ := hwsQ2
    rw [e1, e2, e3, e4]
  refine ⟨hb1ne, ?_, hbeLt, ?_, ?_, ?_, ?_, hwsAll⟩
  · rw [hrfY]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    exact hbeV
  · rw [hrfY]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hpin .x11 (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hx11Q
  · rw [hrfY]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hpin .x13 (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hx13Q
  · rw [hrfY]
    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    rw [hpin .x7 (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hx7Q
  · rw [hrfY]
    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem decStatus_none {bs : List Byte} {off len d : Nat}
    (h : EvmAsm.EL.RLP.Ref.decodeD d (EvmAsm.EL.RLP.Ref.win bs off len)
      = none) : decStatus bs off len d = 1 := by
  unfold decStatus
  rw [h]
  rfl

private theorem decStatus_long_list_zero_at (bs : List Byte) (off len d : Nat)
    (hoff : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 = 0) (hd : 1 ≤ d) :
    decStatus bs off len d = 1 := by
  apply decStatus_none
  rw [show d = (d - 1) + 1 by omega]
  exact EvmAsm.EL.RLP.Ref.decodeD_long_list_zero (d - 1)
    hoff hlo htr hz

private theorem decStatus_long_list_small_at (bs : List Byte) (off len d : Nat)
    (hoff : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hsmall : EvmAsm.EL.RLP.Ref.winBE bs (off + 1)
      ((bs.getD off 0).toNat - 0xF7) < 0x38)
    (hd : 1 ≤ d) : decStatus bs off len d = 1 := by
  apply decStatus_none
  rw [show d = (d - 1) + 1 by omega]
  exact EvmAsm.EL.RLP.Ref.decodeD_long_list_small (d - 1)
    hoff hlo htr hz hsmall

private theorem decStatus_long_list_trunc_at (bs : List Byte) (off len d : Nat)
    (hoff : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : len ≤ (bs.getD off 0).toNat - 0xF7)
    (hlen : 0 < len) (hd : 1 ≤ d) : decStatus bs off len d = 1 := by
  apply decStatus_none
  rw [show d = (d - 1) + 1 by omega]
  exact EvmAsm.EL.RLP.Ref.decodeD_long_list_trunc (d - 1)
    hoff (by omega) hlo htr

private theorem decStatus_long_list_badlen_at (bs : List Byte) (off len d : Nat)
    (hoff : off + len ≤ bs.length)
    (hlo : 0xF8 ≤ (bs.getD off 0).toNat)
    (htr : (bs.getD off 0).toNat - 0xF7 < len)
    (hz : bs.getD (off + 1) 0 ≠ 0)
    (hbig : 0x38 ≤ EvmAsm.EL.RLP.Ref.winBE bs (off + 1)
      ((bs.getD off 0).toNat - 0xF7))
    (hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0xF7)
      + EvmAsm.EL.RLP.Ref.winBE bs (off + 1)
        ((bs.getD off 0).toNat - 0xF7))
    (hd : 1 ≤ d) : decStatus bs off len d = 1 := by
  exact decStatus_none
    (decodeD_long_list_badlen_at bs off len d hoff hlo htr hz hbig hbad hd)

private theorem decStatus_some {bs : List Byte} {off len d : Nat}
    {item : EvmAsm.EL.RLP.RLPItem}
    (h : EvmAsm.EL.RLP.Ref.decodeD d (EvmAsm.EL.RLP.Ref.win bs off len)
      = some item) : decStatus bs off len d = 0 := by
  unfold decStatus
  rw [h]
  rfl

set_option maxRecDepth 8000 in
private theorem post_core_nogo_long (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8)) (A₀ : Assertion) (beS itemsS : FnHandleS)
    (rfR : RegFile) (wsR : List (BitVec 8)) (A : Assertion)
    (rfL : RegFile) (wsL : List (BitVec 8))
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (_hitPost : 1 ≤ d → ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = itemsStatus bs (pStartOf inBase rf₁)
            (pEndOf inBase rf₁ - pStartOf inBase rf₁) (d - 1)
          ∧ rf.get .x13 = fp + 8
          ∧ ws.take 8 = ws₁.take 8
          ∧ A = A₁)
    (hnot : ¬ (Cond.beq .x14 .x0).holds rfL)
    (hrfL : rfR = (execBlock ⟨inBase, bs⟩ fp rfL wsL []).1)
    (hwsL : wsR = (execBlock ⟨inBase, bs⟩ fp rfL wsL []).2)
    (hLong : Stmt.sp ⟨inBase, bs⟩ (⟨fp, 40 * d + 8⟩ : RwRegion)
      (listLongHdr beS) (longHdrReach bs inBase fp d v rf₀ ws₀ A₀)
      rfL wsL A) :
    rfR.get .x14 = decStatus bs off len d ∧ rfR.get .x13 = fp
      ∧ wsR.take 8 = dwordBytes v ∧ A = A₀ := by
  rw [listLongHdr] at hLong
  simp only [longHdrReach, Stmt.sp] at hLong
  simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem, aluSem,
    RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true] at hLong
  rcases hLong with TR | ⟨rfW, wsW, hlenW,
    ⟨⟨rfB1, wsB1, hlenB1, INNER2, hrfB1, hwsB1⟩, hltr⟩,
    hrfW, hwsW⟩
  · rcases TR with TR | TR
    · obtain ⟨rfT, wsT, hlenT, ⟨INNER1, hlbz⟩, hrfT, hwsT⟩ := TR
      obtain ⟨rfQ, wsQ, hlenQ, hrestQ, hrfQ, hwsQ⟩ := INNER1
      rcases hrestQ with ⟨hrest, hlbtr⟩
      obtain ⟨rfCB, wsCB, hlenCB, hrestCB, hrfCB, hwsCB⟩ := hrest
      rcases hrestCB with ⟨hrestB1, hshortb⟩
      obtain ⟨rfB1, wsB1, hlenB1, hrestB1, hrfB1, hwsB1⟩ := hrestB1
      rcases hrestB1 with ⟨⟨RB0, hshortB1⟩, hbud⟩
      obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
        hrfB0, hwsB0⟩ := RB0
      have hlen0 : 0 < len := by
        rw [h1] at hne
        rcases Nat.eq_zero_or_pos len with hzero | hpos
        · exact absurd (by rw [hx11, hzero]; simp :
            rf₀.get .x11 = rf₀.get .x0) hne
        · exact hpos
      have hoffb : off < bs.length := by omega
      have hlen64 : len < 2 ^ 64 := by
        have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
        have hbs64 : bs.length < 2 ^ 64 := by omega
        omega
      have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
        exact ge_f8_of_short_b0_cb bs inBase fp (40 * d + 8) L
          rf₀ rfB0 rfB1 rfCB wsB0 wsCB hlenB0 off hx10 hoffb h1
          hrfB0 hrfB1 hshortb
      have hx12B1 : rfB1.get .x12 = rf₀.get .x12 := by
        exact b0_x12_raw bs inBase fp rfB0 rf₀ rfB1 wsB0 h1 hrfB0
      have hdpos : 1 ≤ d :=
        one_le_of_x12_notzero d rfB1 rf₀ hbud hx12B1 hx12
      have hpre := long_prefix_f7_facts bs inBase d fp off len v rf₀ ws₀
        rfB0 rfB1 rfCB rfQ wsB0 wsB1 wsCB wsQ L hoff hx10 hx11 hx13
        hlenB0 hlen0 hgeF8 h1 h2 hrfB0 hrfB1 hrfCB hwsB0 hwsB1 (by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hwsCB)
      have hx10Q := hpre.1
      have hx11Q := hpre.2.1
      have hx13Q := hpre.2.2.1
      have hx7Q := hpre.2.2.2.1
      have htkQ := hpre.2.2.2.2.1
      have htr : (bs.getD off 0).toNat - 0xF7 < len := by
        have h := hlbtr
        change BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true at h
        rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
          BitVec.toNat_ofNat] at h
        have hnlt : (bs.getD off 0).toNat - 0xF7 < 2 ^ 64 := by
          have hb : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
          omega
        rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
        exact h
      have hoff1 : off + 1 < bs.length := by omega
      have haddr1 : rfQ.get .x10 + signExtend12 (1 : BitVec 12)
          = inBase + BitVec.ofNat 64 (off + 1) := by
        rw [se12_1, hx10Q]
        bv_omega
      have hnorw1 : ¬ inRw fp wsQ
          (rfQ.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
        rw [haddr1]
        exact L.not_inRw hlenQ hoff1
      have hstep : (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
          [.LBU .x6 .x10 1]).1 =
          rfQ.set .x6 ((bs.getD (off + 1) 0).zeroExtend 64) := by
        simp only [execBlock_cons, execBlock_nil]
        rw [lbu_ro _ _ _ _ _ _ _ hnorw1, haddr1,
          region_byteAt L.regWf hoff1]
      have hz : bs.getD (off + 1) 0 = 0 := by
        have h : rfT.get .x6 = rfT.get .x0 := hlbz
        have hrfQ' : rfT = rfQ.set .x6
            ((bs.getD (off + 1) 0).zeroExtend 64) := by
          calc
            rfT = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
              [.LBU .x6 .x10 1]).1 := hrfQ
            _ = _ := hstep
        rw [hrfQ'] at h
        simp only [RegFile.get_set_self, RegFile.get_x0, ne_eq,
          reduceCtorEq, not_false_eq_true] at h
        apply BitVec.eq_of_toNat_eq
        have hh := congrArg BitVec.toNat h
        rw [toNat_zx] at hh
        simpa using hh
      have hrfR' : rfR = rfL := by simpa using hrfL
      have hrfR14 : rfR.get .x14 = (1 : Word) := by
        rw [hrfR', hrfT]
        simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
          not_false_eq_true]
      have hx13T : rfT.get .x13 = fp := by
        have hrfQ' : rfT = rfQ.set .x6
            ((bs.getD (off + 1) 0).zeroExtend 64) := by
          calc
            rfT = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
              [.LBU .x6 .x10 1]).1 := hrfQ
            _ = _ := hstep
        rw [hrfQ']
        simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        exact hx13Q
      have hrfR13 : rfR.get .x13 = fp := by
        rw [hrfR', hrfT]
        simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
          not_false_eq_true]
        exact hx13T
      have hwsR' : wsR = wsL := by simpa using hwsL
      have htk : wsR.take 8 = dwordBytes v := by
        rw [hwsR', hwsT, hwsQ]
        exact htkQ
      refine ⟨?_, hrfR13, htk, h3⟩
      rw [decStatus_long_list_zero_at bs off len d hoff hgeF8 htr hz hdpos]
      exact hrfR14
    · rcases TR with SM | GO_BAD
      case _ =>
        -- st_llsmall: the BE length value is < 0x38 (non-canonical header)
        obtain ⟨rfX, wsX, hlenX, ⟨⟨rfY, wsY, hlenY, hcall3, hrfX, hwsX⟩,
          hsmall⟩, hrfLx, hwsLx⟩ := SM
        obtain ⟨rfP0, wsP0, AP0, hpreCall, hpre, hpost⟩ := hcall3
        obtain ⟨rfT, wsT, hlenT, ⟨hQnode, hnlbz⟩, hrfP0, hwsP0⟩ := hpreCall
        obtain ⟨rfQ, wsQ, hlenQ, ⟨hSBnode, hlltr2⟩, hrfT, hwsT⟩ := hQnode
        obtain ⟨rfSB, wsSB, hlenSB, ⟨hCBnode, hshortb⟩, hrfQr, hwsQr⟩ :=
          hSBnode
        obtain ⟨rfCB, wsCB, hlenCB, ⟨⟨hex, -⟩, hbud⟩, hrfSBr, hwsSBr⟩ :=
          hCBnode
        obtain ⟨r0, s0, hlens0, ⟨⟨h1, h2, h3⟩, hne⟩, hrfCBr, hwsCBr⟩ := hex
        have hlen0 : 0 < len := by
          rw [h1] at hne
          rcases Nat.eq_zero_or_pos len with hzero | hpos
          · exact absurd (by rw [hx11, hzero]; simp :
              rf₀.get .x11 = rf₀.get .x0) hne
          · exact hpos
        have hoffb : off < bs.length := by omega
        have haddr : r0.get .x10 + signExtend12 (0 : BitVec 12)
            = inBase + BitVec.ofNat 64 off := by
          rw [se12_0, h1, hx10]
          bv_omega
        have hnorw : ¬ inRw fp s0
            (r0.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
          rw [haddr]
          exact L.not_inRw hlens0 hoffb
        rw [if_neg hnorw, haddr, region_byteAt L.regWf hoffb] at hrfCBr
        have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
          have h : ¬ BitVec.ult (rfSB.get .x5) (rfSB.get .x6) = true :=
            hshortb
          exact ge_f8_of_short_blocks (bs.getD off 0) r0 rfCB rfSB _
            hrfCBr hrfSBr h
        have hx12CB : rfCB.get .x12 = rf₀.get .x12 := by
          rw [hrfCBr, h1]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
        have hdpos : 1 ≤ d := one_le_of_x12_notzero d rfCB rf₀ hbud
          hx12CB hx12
        -- repackage the melted engine equations in `execBlock` form
        have hrfCBe : rfCB = (execBlock ⟨inBase, bs⟩ fp r0 s0
            [.LBU .x5 .x10 0, .LI .x6 0xC0]).1 := by
          rw [b0_engine bs inBase fp _ L r0 s0 hlens0 off
            (by rw [h1]; exact hx10) hoffb]
          exact hrfCBr
        have hwsCBe : wsCB = (execBlock ⟨inBase, bs⟩ fp r0 s0
            [.LBU .x5 .x10 0, .LI .x6 0xC0]).2 := by
          rw [b0_ws]
          exact hwsCBr
        have hrfSBe : rfSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
            [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hrfSBr
        have hwsSBe : wsSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
            [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).2 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hwsSBr
        have hrfQe : rfQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
            [.ADDI .x7 .x5 (-0xF7)]).1 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hrfQr
        have hwsQe : wsQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
            [.ADDI .x7 .x5 (-0xF7)]).2 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hwsQr
        obtain ⟨hx10Q, hx11Q, hx13Q, hx7Q, htkQ, hwqQ⟩ :=
          long_prefix_f7_facts bs inBase d fp off len v rf₀ ws₀
            r0 rfCB rfSB rfQ s0 wsCB wsSB wsQ L hoff hx10 hx11 hx13
            hlens0 hlen0 hgeF8 h1 h2 hrfCBe hrfSBe hrfQe hwsCBe hwsSBe
            hwsQe
        have hlen64 : len < 2 ^ 64 := by
          have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
          omega
        have htr : (bs.getD off 0).toNat - 0xF7 < len := by
          have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true := hlltr2
          rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat] at h
          have hnlt : (bs.getD off 0).toNat - 0xF7 < 2 ^ 64 := by
            have hb : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
            omega
          rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
          exact h
        have hrfTe : rfT = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
            [.LBU .x6 .x10 1]).1 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem,
            aluSem]
          exact hrfT
        have hwsTe : wsT = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
            [.LBU .x6 .x10 1]).2 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem,
            aluSem]
          exact hwsT
        have hrfP0e : rfP0 = (execBlock ⟨inBase, bs⟩ fp rfT wsT
            [.ADDI .x29 .x10 1, .MV .x30 .x7]).1 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
            RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
          exact hrfP0
        have hwsP0e : wsP0 = (execBlock ⟨inBase, bs⟩ fp rfT wsT
            [.ADDI .x29 .x10 1, .MV .x30 .x7]).2 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hwsP0
        have hrfXe : rfX = (execBlock ⟨inBase, bs⟩ fp rfY wsY
            [.LI .x6 0x38]).1 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hrfX
        have hwsXe : wsX = (execBlock ⟨inBase, bs⟩ fp rfY wsY
            [.LI .x6 0x38]).2 := by
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact hwsX
        obtain ⟨hb1ne, hbeV, hbeLt, -, hx13Y, -, hx6Y, hwsYQ⟩ :=
          long_call_facts bs inBase d fp off len rf₀
            rfQ rfT rfP0 rfY rfX wsQ wsT wsP0 wsY wsX AP0 A beS L hoff
            0xF7 (by omega)
            (by have := (bs.getD off 0).isLt; omega) htr
            hx10Q hx11Q hx13Q hx7Q hlenQ hbePost hrfTe hnlbz hrfP0e
            hpost hrfXe hwsTe hwsP0e hwsXe
        have hsmallVal : beVal bs (off + 1)
            ((bs.getD off 0).toNat - 0xF7) < 0x38 := by
          have h : BitVec.ult (rfX.get .x31) (rfX.get .x6) = true := hsmall
          rw [hbeV, hx6Y, ult_iff, BitVec.toNat_ofNat] at h
          rw [Nat.mod_eq_of_lt hbeLt] at h
          exact h
        obtain ⟨-, -, -, hAcall⟩ := hbePost rfP0 wsP0 AP0 rfY wsY A hpost
        have hrfR' : rfR = rfL := by simpa using hrfL
        have hwsR' : wsR = wsL := by simpa using hwsL
        refine ⟨?_, ?_, ?_, hAcall.trans h3⟩
        · rw [hrfR', hrfLx]
          simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [decStatus_long_list_small_at bs off len d hoff hgeF8 htr
            hb1ne (by simpa [beVal_eq_winBE] using hsmallVal)
            hdpos]
        · rw [hrfR', hrfLx]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          exact hx13Y
        · rw [hwsR', hwsLx, hwsYQ]
          exact htkQ
      case _ =>
        rcases GO_BAD with GO | BAD
        case _ =>
          -- llgo sets x14 := 0, contradicting the poisoned-branch premise
          obtain ⟨rfF, wsF, -, -, hrfLg, -⟩ := GO
          apply False.elim
          apply hnot
          change rfL.get .x14 = rfL.get .x0
          rw [hrfLg]
          simp only [RegFile.get_set_self, RegFile.get_x0, ne_eq,
            reduceCtorEq, not_false_eq_true]
        case _ =>
          -- st_badLL: window length disagrees with 1 + ll + value
          obtain ⟨rfF, wsF, hlenF, ⟨⟨rfX, wsX, hlenX, ⟨⟨rfY, wsY, hlenY,
            hcall3, hrfX, hwsX⟩, hnsmall⟩, hrfF, hwsF⟩, hbadc⟩, hrfLx,
            hwsLx⟩ := BAD
          obtain ⟨rfP0, wsP0, AP0, hpreCall, hpre, hpost⟩ := hcall3
          obtain ⟨rfT, wsT, hlenT, ⟨hQnode, hnlbz⟩, hrfP0, hwsP0⟩ :=
            hpreCall
          obtain ⟨rfQ, wsQ, hlenQ, ⟨hSBnode, hlltr2⟩, hrfT, hwsT⟩ := hQnode
          obtain ⟨rfSB, wsSB, hlenSB, ⟨hCBnode, hshortb⟩, hrfQr, hwsQr⟩ :=
            hSBnode
          obtain ⟨rfCB, wsCB, hlenCB, ⟨⟨hex, -⟩, hbud⟩, hrfSBr, hwsSBr⟩ :=
            hCBnode
          obtain ⟨r0, s0, hlens0, ⟨⟨h1, h2, h3⟩, hne⟩, hrfCBr, hwsCBr⟩ :=
            hex
          have hlen0 : 0 < len := by
            rw [h1] at hne
            rcases Nat.eq_zero_or_pos len with hzero | hpos
            · exact absurd (by rw [hx11, hzero]; simp :
                rf₀.get .x11 = rf₀.get .x0) hne
            · exact hpos
          have hoffb : off < bs.length := by omega
          have haddr : r0.get .x10 + signExtend12 (0 : BitVec 12)
              = inBase + BitVec.ofNat 64 off := by
            rw [se12_0, h1, hx10]
            bv_omega
          have hnorw : ¬ inRw fp s0
              (r0.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
            rw [haddr]
            exact L.not_inRw hlens0 hoffb
          rw [if_neg hnorw, haddr, region_byteAt L.regWf hoffb] at hrfCBr
          have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
            have h : ¬ BitVec.ult (rfSB.get .x5) (rfSB.get .x6) = true :=
              hshortb
            exact ge_f8_of_short_blocks (bs.getD off 0) r0 rfCB rfSB _
              hrfCBr hrfSBr h
          have hx12CB : rfCB.get .x12 = rf₀.get .x12 := by
            rw [hrfCBr, h1]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
          have hdpos : 1 ≤ d := one_le_of_x12_notzero d rfCB rf₀ hbud
            hx12CB hx12
          have hrfCBe : rfCB = (execBlock ⟨inBase, bs⟩ fp r0 s0
              [.LBU .x5 .x10 0, .LI .x6 0xC0]).1 := by
            rw [b0_engine bs inBase fp _ L r0 s0 hlens0 off
              (by rw [h1]; exact hx10) hoffb]
            exact hrfCBr
          have hwsCBe : wsCB = (execBlock ⟨inBase, bs⟩ fp r0 s0
              [.LBU .x5 .x10 0, .LI .x6 0xC0]).2 := by
            rw [b0_ws]
            exact hwsCBr
          have hrfSBe : rfSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
              [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).1 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hrfSBr
          have hwsSBe : wsSB = (execBlock ⟨inBase, bs⟩ fp rfCB wsCB
              [.ADDI .x12 .x12 (-1), .LI .x6 0xF8]).2 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hwsSBr
          have hrfQe : rfQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
              [.ADDI .x7 .x5 (-0xF7)]).1 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hrfQr
          have hwsQe : wsQ = (execBlock ⟨inBase, bs⟩ fp rfSB wsSB
              [.ADDI .x7 .x5 (-0xF7)]).2 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hwsQr
          obtain ⟨hx10Q, hx11Q, hx13Q, hx7Q, htkQ, hwqQ⟩ :=
            long_prefix_f7_facts bs inBase d fp off len v rf₀ ws₀
              r0 rfCB rfSB rfQ s0 wsCB wsSB wsQ L hoff hx10 hx11 hx13
              hlens0 hlen0 hgeF8 h1 h2 hrfCBe hrfSBe hrfQe hwsCBe hwsSBe
              hwsQe
          have hlen64 : len < 2 ^ 64 := by
            have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
            omega
          have htr : (bs.getD off 0).toNat - 0xF7 < len := by
            have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
              hlltr2
            rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat] at h
            have hnlt : (bs.getD off 0).toNat - 0xF7 < 2 ^ 64 := by
              have hb : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
              omega
            rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
            exact h
          have hrfTe : rfT = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
              [.LBU .x6 .x10 1]).1 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem,
              aluSem]
            exact hrfT
          have hwsTe : wsT = (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
              [.LBU .x6 .x10 1]).2 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, loadSem,
              aluSem]
            exact hwsT
          have hrfP0e : rfP0 = (execBlock ⟨inBase, bs⟩ fp rfT wsT
              [.ADDI .x29 .x10 1, .MV .x30 .x7]).1 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
              RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
            exact hrfP0
          have hwsP0e : wsP0 = (execBlock ⟨inBase, bs⟩ fp rfT wsT
              [.ADDI .x29 .x10 1, .MV .x30 .x7]).2 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hwsP0
          have hrfXe : rfX = (execBlock ⟨inBase, bs⟩ fp rfY wsY
              [.LI .x6 0x38]).1 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hrfX
          have hwsXe : wsX = (execBlock ⟨inBase, bs⟩ fp rfY wsY
              [.LI .x6 0x38]).2 := by
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            exact hwsX
          obtain ⟨hb1ne, hbeV, hbeLt, hx11Y, hx13Y, hx7Y, hx6Y, hwsYQ⟩ :=
            long_call_facts bs inBase d fp off len rf₀
              rfQ rfT rfP0 rfY rfX wsQ wsT wsP0 wsY wsX AP0 A beS L hoff
              0xF7 (by omega)
              (by have := (bs.getD off 0).isLt; omega) htr
              hx10Q hx11Q hx13Q hx7Q hlenQ hbePost hrfTe hnlbz hrfP0e
              hpost hrfXe hwsTe hwsP0e hwsXe
          have hbig : 0x38 ≤ beVal bs (off + 1)
              ((bs.getD off 0).toNat - 0xF7) := by
            have h : ¬ BitVec.ult (rfX.get .x31) (rfX.get .x6) = true :=
              hnsmall
            rw [hbeV, hx6Y, ult_iff, BitVec.toNat_ofNat] at h
            rw [Nat.mod_eq_of_lt hbeLt] at h
            have h38 : ((0x38 : Word)).toNat = 0x38 := rfl
            rw [h38] at h
            omega
          have hx31F : rfF.get .x31 = rfX.get .x31 := by
            rw [hrfF]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
          have hx6F : rfF.get .x6 = BitVec.ofNat 64
              (len - 1 - ((bs.getD off 0).toNat - 0xF7)) := by
            rw [hrfF]
            simp only [RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hx11Y, hx7Y, se12_n1]
            have h1lt : 1 ≤ len := hlen0
            have hlt : (bs.getD off 0).toNat - 0xF7 < len := htr
            bv_omega
          have hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0xF7)
              + beVal bs (off + 1) ((bs.getD off 0).toNat - 0xF7) := by
            intro hcontra
            apply hbadc
            show rfF.get .x31 = rfF.get .x6
            rw [hx31F, hbeV, hx6F]
            congr 1
            omega
          obtain ⟨-, -, -, hAcall⟩ := hbePost rfP0 wsP0 AP0 rfY wsY A hpost
          have hrfR' : rfR = rfL := by simpa using hrfL
          have hwsR' : wsR = wsL := by simpa using hwsL
          refine ⟨?_, ?_, ?_, hAcall.trans h3⟩
          · rw [hrfR', hrfLx]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [decStatus_long_list_badlen_at bs off len d hoff hgeF8 htr
              hb1ne
              (by simpa [beVal_eq_winBE] using hbig)
              (by simpa [beVal_eq_winBE] using hbad) hdpos]
          · rw [hrfR', hrfLx, hrfF]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hx13Y
          · rw [hwsR', hwsLx, hwsF, hwsYQ]
            exact htkQ
  · -- st_lltr: the length-of-length field overruns the window
    obtain ⟨⟨rf1, ws1, -, ⟨⟨⟨hex, -⟩, hbud⟩, hrfB1e, hwsB1e⟩⟩, hgef8c⟩ :=
      INNER2
    obtain ⟨r0, s0, hlens0, ⟨⟨h1, h2, h3⟩, hne⟩, hrf1e, hws1e⟩ := hex
    have hlen0 : 0 < len := by
      rw [h1] at hne
      rcases Nat.eq_zero_or_pos len with hzero | hpos
      · exact absurd (by rw [hx11, hzero]; simp :
          rf₀.get .x11 = rf₀.get .x0) hne
      · exact hpos
    have hoffb : off < bs.length := by omega
    have hlen64 : len < 2 ^ 64 := by
      have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
      omega
    have haddr : r0.get .x10 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 off := by
      rw [se12_0, h1, hx10]
      bv_omega
    have hnorw : ¬ inRw fp s0
        (r0.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
      rw [haddr]
      exact L.not_inRw hlens0 hoffb
    rw [if_neg hnorw, haddr, region_byteAt L.regWf hoffb] at hrf1e
    have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
      have h : ¬ BitVec.ult (rfB1.get .x5) (rfB1.get .x6) = true := hgef8c
      exact ge_f8_of_short_blocks (bs.getD off 0) r0 rf1 rfB1 _ hrf1e
        hrfB1e h
    have hx12r1 : rf1.get .x12 = rf₀.get .x12 := by
      rw [hrf1e, h1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    have hdpos : 1 ≤ d := one_le_of_x12_notzero d rf1 rf₀ hbud hx12r1 hx12
    have hx5B1 : rfB1.get .x5 = (bs.getD off 0).zeroExtend 64 := by
      rw [hrfB1e, hrf1e]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true]
    have hx11B1 : rfB1.get .x11 = BitVec.ofNat 64 len := by
      rw [hrfB1e, hrf1e, h1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx11
    have htr : len ≤ (bs.getD off 0).toNat - 0xF7 := by
      have h : ¬ BitVec.ult (rfW.get .x7) (rfW.get .x11) = true := hltr
      rw [hrfB1] at h
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true] at h
      rw [hx5B1, hx11B1, se12_nF7] at h
      have hb : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
      have h7 : ((bs.getD off 0).zeroExtend 64 + (-0xF7 : Word)).toNat
          = (bs.getD off 0).toNat - 0xF7 := by
        have hcm : ((-0xF7 : Word)).toNat = 2 ^ 64 - 0xF7 := by decide
        rw [BitVec.toNat_add, toNat_zx, hcm]
        omega
      rw [ult_iff, h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] at h
      omega
    have hrfR' : rfR = rfL := by simpa using hrfL
    have hwsR' : wsR = wsL := by simpa using hwsL
    have hrfR14 : rfR.get .x14 = (1 : Word) := by
      rw [hrfR', hrfW]
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
    have hrfR13 : rfR.get .x13 = fp := by
      rw [hrfR', hrfW, hrfB1, hrfB1e, hrf1e, h1]
      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
      exact hx13
    have htk : wsR.take 8 = dwordBytes v := by
      rw [hwsR', hwsW, hwsB1, hwsB1e, hws1e, h2]
      have hs := setBytes_slot ws₀ (dwordBytes v) 0
        (by
          rw [length_dwordBytes]
          have hh := hlens0
          rw [h2, length_setBytes] at hh
          omega)
      rw [List.drop_zero, length_dwordBytes] at hs
      exact hs
    refine ⟨?_, hrfR13, htk, h3⟩
    rw [decStatus_long_list_trunc_at bs off len d hoff hgeF8 htr hlen0 hdpos]
    exact hrfR14

set_option maxRecDepth 8000 in
private theorem post_core (bs : List Byte) (inBase : Word) (d : Nat)
    (fp : Word) (off len : Nat) (v : Word) (rf₀ : RegFile)
    (ws₀ : List (BitVec 8)) (A₀ : Assertion) (beS itemsS : FnHandleS)
    (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (hd64 : d < 2 ^ 64)
    (hbePost : ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8)) (A₁ : Assertion)
        (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        beS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x31 = BitVec.ofNat 64
            (beVal bs (idxOf inBase (rf₁.get .x29)) (rf₁.get .x30).toNat)
          ∧ (∀ r : Reg, r ≠ .x28 → r ≠ .x29 → r ≠ .x30 → r ≠ .x31 →
              rf.get r = rf₁.get r)
          ∧ ws = ws₁ ∧ A = A₁)
    (hitPost : 1 ≤ d → ∀ (rf₁ : RegFile) (ws₁ : List (BitVec 8))
        (A₁ : Assertion) (rf : RegFile) (ws : List (BitVec 8)) (A : Assertion),
        itemsS.post rf₁ ws₁ A₁ rf ws A →
        rf.get .x10 = itemsStatus bs (pStartOf inBase rf₁)
            (pEndOf inBase rf₁ - pStartOf inBase rf₁) (d - 1)
          ∧ rf.get .x13 = fp + 8
          ∧ ws.take 8 = ws₁.take 8
          ∧ A = A₁)
    (hsp : Stmt.sp ⟨inBase, bs⟩ (⟨fp, 40 * d + 8⟩ : RwRegion)
      (decBody beS itemsS)
      (Reach.exact rf₀ (setBytes ws₀ 0 (dwordBytes v)) A₀) rf ws A) :
    decPostV bs inBase d fp off len v A₀ rf ws A := by
  have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
  have hblen : bs.length < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  obtain ⟨rfR, wsR, hlenR, ITE, hrf, hws⟩ := hsp
  have hws' : ws = wsR := hws
  -- reduce to the pre-return state
  suffices hPR : rfR.get .x14 = decStatus bs off len d ∧ rfR.get .x13 = fp
      ∧ wsR.take 8 = dwordBytes v ∧ A = A₀ by
    obtain ⟨hs14, hs13, hstk, hsA⟩ := hPR
    subst hrf
    refine ⟨?_, ?_, ?_, hsA⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      exact hs14
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hs13
    · rw [hws']
      exact hstk
  rcases ITE with TARM | EARM
  · -- empty window: reject
    obtain ⟨rfE', wsE', hlenE', ⟨⟨h1, h2, h3⟩, hcond⟩, hrfR, hwsR⟩ := TARM
    rw [h1] at hcond hrfR
    have hlen0 : len = 0 := by
      have h : rf₀.get .x11 = rf₀.get .x0 := hcond
      rw [hx11] at h
      simp only [RegFile.get_x0] at h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat] at this
      simp at this
      omega
    refine ⟨?_, ?_, ?_, h3⟩
    · rw [hrfR]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      rw [hlen0, decStatus_none (EvmAsm.EL.RLP.Ref.decodeD_len_zero d bs off)]
    · rw [hrfR]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hx13
    · have hwsR' : wsR = wsE' := hwsR
      rw [hwsR', h2]
      have hs := setBytes_slot ws₀ (dwordBytes v) 0
        (by
          rw [length_dwordBytes]
          have : wsE'.length = 40 * d + 8 := hlenE'
          rw [h2, length_setBytes] at this
          omega)
      rw [List.drop_zero, length_dwordBytes] at hs
      exact hs
  -- nonempty: b0 loaded, dispatch
  rcases EARM with BY | LI
  · -- byte-string arms
    rcases BY with SG | SBLB
    · -- single-byte sub-arm: two leaves
      rcases SG with OK1 | BAD1
      · obtain ⟨rfS, wsS, hlenS, ⟨⟨rfT, wsT, hlenT, ⟨⟨rfU, wsU, hlenU,
          ⟨⟨rfV, wsV, hlenV, ⟨⟨h1, h2, h3⟩, hne⟩, hrfU, hwsU⟩, hdisp⟩,
          hrfT, hwsT⟩, hsingle⟩, hrfS, hwsS⟩, hlen1⟩, hrfR, hwsR⟩ := OK1
        rw [h1] at hne hrfU
        have hlen0 : 0 < len := by
          rcases Nat.eq_zero_or_pos len with h0 | hp
          · exact absurd (by rw [hx11, h0]; simp :
              rf₀.get .x11 = rf₀.get .x0) hne
          · exact hp
        have hoffb : off < bs.length := by omega
        rw [b0_engine bs inBase fp _ L rf₀ wsV hlenV off hx10 hoffb] at hrfU
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hrfT hrfS hrfR
        have hv5U : rfU.get .x5 = (bs.getD off 0).zeroExtend 64 := by
          rw [hrfU]
          simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
            reduceCtorEq, not_false_eq_true]
        have hb0lt : (bs.getD off 0).toNat < 0x80 := by
          have h : BitVec.ult (rfT.get .x5) (rfT.get .x6) = true := hsingle
          rw [show rfT.get .x5 = (bs.getD off 0).zeroExtend 64 from by
              rw [hrfT]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hv5U,
            show rfT.get .x6 = (0x80 : Word) from by
              rw [hrfT]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]] at h
          rw [ult_iff, toNat_zx] at h
          have hc : ((0x80 : Word)).toNat = 0x80 := rfl
          omega
        have hlen1' : len = 1 := by
          have h : rfS.get .x11 = rfS.get .x6 := hlen1
          rw [show rfS.get .x6 = (1 : Word) from by
              rw [hrfS]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true],
            show rfS.get .x11 = BitVec.ofNat 64 len from by
              rw [hrfS]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hrfT]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hrfU]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hx11] at h
          have := congrArg BitVec.toNat h
          rw [BitVec.toNat_ofNat] at this
          have h1n : ((1 : Word)).toNat = 1 := rfl
          omega
        refine ⟨?_, ?_, ?_, h3⟩
        · rw [hrfR]
          simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hlen1', decStatus_some
            (EvmAsm.EL.RLP.Ref.decodeD_single_ok d (by omega) hb0lt)]
        · rw [hrfR]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hrfS]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hrfT]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hrfU]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          exact hx13
        · have hwq : wsR = setBytes ws₀ 0 (dwordBytes v) := by
            have e1 : wsR = wsS := hwsR
            have e2 : wsS = wsT := hwsS
            have e3 : wsT = wsU := hwsT
            have e4 : wsU = wsV := hwsU
            rw [e1, e2, e3, e4, h2]
          rw [hwq]
          have hs := setBytes_slot ws₀ (dwordBytes v) 0
            (by
              rw [length_dwordBytes]
              have hl : wsV.length = 40 * d + 8 := hlenV
              rw [h2, length_setBytes] at hl
              omega)
          rw [List.drop_zero, length_dwordBytes] at hs
          exact hs
      · obtain ⟨rfS, wsS, hlenS, ⟨⟨rfT, wsT, hlenT, ⟨⟨rfU, wsU, hlenU,
          ⟨⟨rfV, wsV, hlenV, ⟨⟨h1, h2, h3⟩, hne⟩, hrfU, hwsU⟩, hdisp⟩,
          hrfT, hwsT⟩, hsingle⟩, hrfS, hwsS⟩, hnlen1⟩, hrfR, hwsR⟩ := BAD1
        rw [h1] at hne hrfU
        have hlen0 : 0 < len := by
          rcases Nat.eq_zero_or_pos len with h0 | hp
          · exact absurd (by rw [hx11, h0]; simp :
              rf₀.get .x11 = rf₀.get .x0) hne
          · exact hp
        have hoffb : off < bs.length := by omega
        rw [b0_engine bs inBase fp _ L rf₀ wsV hlenV off hx10 hoffb] at hrfU
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hrfT hrfS hrfR
        have hv5U : rfU.get .x5 = (bs.getD off 0).zeroExtend 64 := by
          rw [hrfU]
          simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
            reduceCtorEq, not_false_eq_true]
        have hb0lt : (bs.getD off 0).toNat < 0x80 := by
          have h : BitVec.ult (rfT.get .x5) (rfT.get .x6) = true := hsingle
          rw [show rfT.get .x5 = (bs.getD off 0).zeroExtend 64 from by
              rw [hrfT]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hv5U,
            show rfT.get .x6 = (0x80 : Word) from by
              rw [hrfT]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]] at h
          rw [ult_iff, toNat_zx] at h
          have hc : ((0x80 : Word)).toNat = 0x80 := rfl
          omega
        have hlenne1 : len ≠ 1 := by
          intro hcontra
          apply hnlen1
          show rfS.get .x11 = rfS.get .x6
          rw [show rfS.get .x6 = (1 : Word) from by
              rw [hrfS]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true],
            show rfS.get .x11 = BitVec.ofNat 64 len from by
              rw [hrfS]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hrfT]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hrfU]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hx11, hcontra]
          rfl
        refine ⟨?_, ?_, ?_, h3⟩
        · rw [hrfR]
          simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [decStatus_none
            (EvmAsm.EL.RLP.Ref.decodeD_single_long d hoff (by omega) hb0lt)]
        · rw [hrfR]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hrfS]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hrfT]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          rw [hrfU]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
            not_false_eq_true]
          exact hx13
        · have hwq : wsR = setBytes ws₀ 0 (dwordBytes v) := by
            have e1 : wsR = wsS := hwsR
            have e2 : wsS = wsT := hwsS
            have e3 : wsT = wsU := hwsT
            have e4 : wsU = wsV := hwsU
            rw [e1, e2, e3, e4, h2]
          rw [hwq]
          have hs := setBytes_slot ws₀ (dwordBytes v) 0
            (by
              rw [length_dwordBytes]
              have hl : wsV.length = 40 * d + 8 := hlenV
              rw [h2, length_setBytes] at hl
              omega)
          rw [List.drop_zero, length_dwordBytes] at hs
          exact hs
    · -- short/long byte-string arms
      rcases SBLB with SB | LB
      · -- short byte string: four leaves
        -- shared: destructure to the sb-block state per leaf
        rcases SB with FIT | ⟨rfW, wsW, hlenW, ⟨⟨rfX2, wsX2, hlenX2,
          ⟨⟨rfY2, wsY2, hlenY2, ⟨⟨rfZ2, wsZ2, hlenZ2, ⟨⟨rfV, wsV, hlenV,
          ⟨⟨h1, h2, h3⟩, hne⟩, hrfZ2, hwsZ2⟩, hdisp⟩, hrfY2, hwsY2⟩,
          hnsingle⟩, hrfX2, hwsX2⟩, hshortb⟩, hrfW, hwsW⟩, hnsbfit⟩,
          hrfR, hwsR⟩
        case _ =>  -- sbfit taken: three deeper leaves
          rcases FIT with CANONT | OK3
          · rcases CANONT with NC | OK2
            · -- st_noncanon
              obtain ⟨rfNC, wsNC, hlenNC, ⟨RB1, hsbc2⟩, hrfR, hwsR⟩ := NC
              obtain ⟨rfB1s, wsB1s, hlenB1s, ⟨RS1, hsbcanon⟩, hrfB1,
                hwsB1⟩ := RB1
              obtain ⟨rfS1, wsS1, hlenS1, ⟨RSB, hsbfit⟩, hrfS1, hwsS1⟩ := RS1
              obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩, hrfSB, hwsSB⟩ := RSB
              obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩, hrfCB,
                hwsCB⟩ := RCB
              obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩, hrfC8, hwsC8⟩ := RC8
              obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩, hrfB0,
                hwsB0⟩ := RB0
              obtain ⟨hge80, hleB7, hfit, hx10Q, hx13Q, hx7Q, htkQ, hwqQ⟩ :=
                short_fit_facts bs inBase d fp off len v rf₀ ws₀ rfB0 rfC8
                  rfCB rfSB rfS1 rfB1s wsB0 wsC8 wsCB wsSB wsS1 wsB1s L hoff
                  hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hrfC8 hnsingle hrfCB
                  hshortb hrfSB hsbfit hrfS1 hwsB0 hwsC8 hwsCB hwsSB hwsS1
              have hlr1 : (bs.getD off 0).toNat - 0x80 = 1 := by
                have h : rfB1s.get .x7 = rfB1s.get .x6 := hsbcanon
                rw [hx7Q, show rfB1s.get .x6 = (1 : Word) from by
                  rw [hrfS1]
                  simp only [execBlock_cons, execBlock_nil, execInstrRF,
                    aluSem]
                  simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]] at h
                have := congrArg BitVec.toNat h
                rw [BitVec.toNat_ofNat] at this
                have h1n : ((1 : Word)).toNat = 1 := rfl
                omega
              have hlen2 : len = 2 := by omega
              have hoff2 : off + 2 ≤ bs.length := by omega
              have hb081 : (bs.getD off 0).toNat = 0x81 := by omega
              -- resolve the second-byte load
              have haddr1 : rfB1s.get .x10 + signExtend12 (1 : BitVec 12)
                  = inBase + BitVec.ofNat 64 (off + 1) := by
                rw [se12_1, hx10Q]
                have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
                bv_omega
              have hlenB1s' : wsB1s.length = 40 * d + 8 := by
                rw [hwqQ, length_setBytes]
                have hl : wsB0.length = 40 * d + 8 := hlenB0
                rw [h2, length_setBytes] at hl
                exact hl
              have hnorw1 : ¬ inRw fp wsB1s
                  (rfB1s.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
                rw [haddr1]
                exact L.not_inRw hlenB1s' (by omega)
              rw [show (execBlock ⟨inBase, bs⟩ fp rfB1s wsB1s
                  [.LBU .x6 .x10 1, .LI .x7 0x80]).1
                = ((rfB1s.set .x6
                    ((bs.getD (off + 1) 0).zeroExtend 64)).set .x7 0x80)
                from by
                  simp only [execBlock_cons, execBlock_nil]
                  rw [lbu_ro _ _ _ _ _ _ _ hnorw1]
                  simp only [execInstrRF, aluSem]
                  rw [haddr1, region_byteAt L.regWf (by omega)]] at hrfB1
              have hb1lt : (bs.getD (off + 1) 0).toNat < 0x80 := by
                have h : BitVec.ult (rfNC.get .x6) (rfNC.get .x7)
                    = true := hsbc2
                rw [show rfNC.get .x6
                    = (bs.getD (off + 1) 0).zeroExtend 64 from by
                    rw [hrfB1]
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true],
                  show rfNC.get .x7 = (0x80 : Word) from by
                    rw [hrfB1]
                    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                      not_false_eq_true]] at h
                rw [ult_iff, toNat_zx] at h
                have hc : ((0x80 : Word)).toNat = 0x80 := rfl
                omega
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                at hrfR
              refine ⟨?_, ?_, ?_, h3⟩
              · rw [hrfR]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hlen2, decStatus_none
                  (EvmAsm.EL.RLP.Ref.decodeD_short_bytes_noncanon d hoff2
                    hb081 hb1lt)]
              · rw [hrfR]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB1]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx13Q
              · have e1 : wsR = wsNC := hwsR
                have e2 : wsNC = wsB1s := hwsB1
                rw [e1, e2]
                exact htkQ
            · -- st_ok2
              obtain ⟨rfNC, wsNC, hlenNC, ⟨RB1, hnsbc2⟩, hrfR, hwsR⟩ := OK2
              obtain ⟨rfB1s, wsB1s, hlenB1s, ⟨RS1, hsbcanon⟩, hrfB1,
                hwsB1⟩ := RB1
              obtain ⟨rfS1, wsS1, hlenS1, ⟨RSB, hsbfit⟩, hrfS1, hwsS1⟩ := RS1
              obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩, hrfSB, hwsSB⟩ := RSB
              obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩, hrfCB,
                hwsCB⟩ := RCB
              obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩, hrfC8, hwsC8⟩ := RC8
              obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩, hrfB0,
                hwsB0⟩ := RB0
              obtain ⟨hge80, hleB7, hfit, hx10Q, hx13Q, hx7Q, htkQ, hwqQ⟩ :=
                short_fit_facts bs inBase d fp off len v rf₀ ws₀ rfB0 rfC8
                  rfCB rfSB rfS1 rfB1s wsB0 wsC8 wsCB wsSB wsS1 wsB1s L hoff
                  hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hrfC8 hnsingle hrfCB
                  hshortb hrfSB hsbfit hrfS1 hwsB0 hwsC8 hwsCB hwsSB hwsS1
              have hlr1 : (bs.getD off 0).toNat - 0x80 = 1 := by
                have h : rfB1s.get .x7 = rfB1s.get .x6 := hsbcanon
                rw [hx7Q, show rfB1s.get .x6 = (1 : Word) from by
                  rw [hrfS1]
                  simp only [execBlock_cons, execBlock_nil, execInstrRF,
                    aluSem]
                  simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]] at h
                have := congrArg BitVec.toNat h
                rw [BitVec.toNat_ofNat] at this
                have h1n : ((1 : Word)).toNat = 1 := rfl
                omega
              have hoff2 : off + 2 ≤ bs.length := by omega
              have haddr1 : rfB1s.get .x10 + signExtend12 (1 : BitVec 12)
                  = inBase + BitVec.ofNat 64 (off + 1) := by
                rw [se12_1, hx10Q]
                have hwfr : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
                bv_omega
              have hlenB1s' : wsB1s.length = 40 * d + 8 := by
                rw [hwqQ, length_setBytes]
                have hl : wsB0.length = 40 * d + 8 := hlenB0
                rw [h2, length_setBytes] at hl
                exact hl
              have hnorw1 : ¬ inRw fp wsB1s
                  (rfB1s.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
                rw [haddr1]
                exact L.not_inRw hlenB1s' (by omega)
              rw [show (execBlock ⟨inBase, bs⟩ fp rfB1s wsB1s
                  [.LBU .x6 .x10 1, .LI .x7 0x80]).1
                = ((rfB1s.set .x6
                    ((bs.getD (off + 1) 0).zeroExtend 64)).set .x7 0x80)
                from by
                  simp only [execBlock_cons, execBlock_nil]
                  rw [lbu_ro _ _ _ _ _ _ _ hnorw1]
                  simp only [execInstrRF, aluSem]
                  rw [haddr1, region_byteAt L.regWf (by omega)]] at hrfB1
              have hb1ge : 0x80 ≤ (bs.getD (off + 1) 0).toNat := by
                have h : ¬ (BitVec.ult (rfNC.get .x6) (rfNC.get .x7)
                    = true) := hnsbc2
                rw [show rfNC.get .x6
                    = (bs.getD (off + 1) 0).zeroExtend 64 from by
                    rw [hrfB1]
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true],
                  show rfNC.get .x7 = (0x80 : Word) from by
                    rw [hrfB1]
                    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                      not_false_eq_true]] at h
                rw [ult_iff, toNat_zx] at h
                have hc : ((0x80 : Word)).toNat = 0x80 := rfl
                omega
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                at hrfR
              refine ⟨?_, ?_, ?_, h3⟩
              · rw [hrfR]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [decStatus_some (EvmAsm.EL.RLP.Ref.decodeD_short_bytes_ok
                  d hoff hge80 hleB7 hfit (fun hc => by omega))]
              · rw [hrfR]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB1]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx13Q
              · have e1 : wsR = wsNC := hwsR
                have e2 : wsNC = wsB1s := hwsB1
                rw [e1, e2]
                exact htkQ
          · -- st_ok3
            obtain ⟨rfO3, wsO3, hlenO3, ⟨RS1, hncanon⟩, hrfR, hwsR⟩ := OK3
            obtain ⟨rfS1, wsS1, hlenS1, ⟨RSB, hsbfit⟩, hrfS1, hwsS1⟩ := RS1
            obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩, hrfSB, hwsSB⟩ := RSB
            obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩, hrfCB, hwsCB⟩ := RCB
            obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩, hrfC8, hwsC8⟩ := RC8
            obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩, hrfB0,
              hwsB0⟩ := RB0
            obtain ⟨hge80, hleB7, hfit, hx10Q, hx13Q, hx7Q, htkQ, hwqQ⟩ :=
              short_fit_facts bs inBase d fp off len v rf₀ ws₀ rfB0 rfC8
                rfCB rfSB rfS1 rfO3 wsB0 wsC8 wsCB wsSB wsS1 wsO3 L hoff
                hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hrfC8 hnsingle hrfCB
                hshortb hrfSB hsbfit hrfS1 hwsB0 hwsC8 hwsCB hwsSB hwsS1
            have hlr1 : (bs.getD off 0).toNat - 0x80 ≠ 1 := by
              intro hcontra
              apply hncanon
              show rfO3.get .x7 = rfO3.get .x6
              rw [hx7Q, hcontra, show rfO3.get .x6 = (1 : Word) from by
                rw [hrfS1]
                simp only [execBlock_cons, execBlock_nil, execInstrRF,
                  aluSem]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]]
              rfl
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
              at hrfR
            refine ⟨?_, ?_, ?_, h3⟩
            · rw [hrfR]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [decStatus_some (EvmAsm.EL.RLP.Ref.decodeD_short_bytes_ok
                d hoff hge80 hleB7 hfit (fun hc => hlr1 (by omega)))]
            · rw [hrfR]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hx13Q
            · have e1 : wsR = wsO3 := hwsR
              rw [e1]
              exact htkQ
        case _ =>  -- st_bad2: length mismatch
          rw [h1] at hne hrfZ2
          have hlen0 : 0 < len := by
            rcases Nat.eq_zero_or_pos len with h0 | hp
            · exact absurd (by rw [hx11, h0]; simp :
                rf₀.get .x11 = rf₀.get .x0) hne
            · exact hp
          have hoffb : off < bs.length := by omega
          rw [b0_engine bs inBase fp _ L rf₀ wsV hlenV off hx10 hoffb]
            at hrfZ2
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            at hrfY2 hrfX2 hrfW hrfR
          have hv5Z : rfZ2.get .x5 = (bs.getD off 0).zeroExtend 64 := by
            rw [hrfZ2]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
          have hv5Y : rfY2.get .x5 = (bs.getD off 0).zeroExtend 64 := by
            rw [hrfY2]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hv5Z
          have hv5X : rfX2.get .x5 = (bs.getD off 0).zeroExtend 64 := by
            rw [hrfX2]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hv5Y
          have hge80 : 0x80 ≤ (bs.getD off 0).toNat := by
            have h : ¬ (BitVec.ult (rfY2.get .x5) (rfY2.get .x6) = true) :=
              hnsingle
            rw [hv5Y, show rfY2.get .x6 = (0x80 : Word) from by
              rw [hrfY2]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]] at h
            rw [ult_iff, toNat_zx] at h
            have hc : ((0x80 : Word)).toNat = 0x80 := rfl
            omega
          have hleB7 : (bs.getD off 0).toNat < 0xB8 := by
            have h : BitVec.ult (rfX2.get .x5) (rfX2.get .x6) = true :=
              hshortb
            rw [hv5X, show rfX2.get .x6 = (0xB8 : Word) from by
              rw [hrfX2]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]] at h
            rw [ult_iff, toNat_zx] at h
            have hc : ((0xB8 : Word)).toNat = 0xB8 := rfl
            omega
          have hbad : len ≠ 1 + ((bs.getD off 0).toNat - 0x80) := by
            intro hcontra
            apply hnsbfit
            show rfW.get .x6 = rfW.get .x11
            have hb0 : (bs.getD off 0).toNat < 256 := (bs.getD off 0).isLt
            rw [show rfW.get .x6
                = BitVec.ofNat 64 ((bs.getD off 0).toNat - 0x80) + 1 from by
                rw [hrfW]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hv5X, se12_n80, se12_1]
                bv_omega,
              show rfW.get .x11 = BitVec.ofNat 64 len from by
                rw [hrfW]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfX2]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfY2]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfZ2]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx11, hcontra]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
            have h1n : ((1 : Word)).toNat = 1 := rfl
            omega
          refine ⟨?_, ?_, ?_, h3⟩
          · rw [hrfR]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [decStatus_none (EvmAsm.EL.RLP.Ref.decodeD_short_bytes_badlen
              d hoff hlen0 hge80 (by omega) hbad)]
          · rw [hrfR]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrfW]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrfX2]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrfY2]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrfZ2]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hx13
          · have hwq : wsR = setBytes ws₀ 0 (dwordBytes v) := by
              have e1 : wsR = wsW := hwsR
              have e2 : wsW = wsX2 := hwsW
              have e3 : wsX2 = wsY2 := hwsX2
              have e4 : wsY2 = wsZ2 := hwsY2
              have e5 : wsZ2 = wsV := hwsZ2
              rw [e1, e2, e3, e4, e5, h2]
            rw [hwq]
            have hs := setBytes_slot ws₀ (dwordBytes v) 0
              (by
                rw [length_dwordBytes]
                have hl : wsV.length = 40 * d + 8 := hlenV
                rw [h2, length_setBytes] at hl
                omega)
            rw [List.drop_zero, length_dwordBytes] at hs
            exact hs
      · -- long byte string
        rcases LB with TR | ⟨rfW, wsW, hlenW,
          ⟨⟨rfB1, wsB1, hlenB1, INNER2, hrfB1, hwsB1⟩, hlbtr⟩,
          hrfW, hwsW⟩
        · rcases TR with TR | TR
          · obtain ⟨rfT, wsT, hlenT, ⟨INNER1, hlbz⟩, hrfT, hwsT⟩ := TR
            obtain ⟨rfQ, wsQ, hlenQ, ⟨INNER2, hlbtr⟩, hrfQ, hwsQ⟩ := INNER1
            obtain ⟨rfB1, wsB1, hlenB1, ⟨RCB, hshortb⟩, hrfB1, hwsB1⟩ := INNER2
            obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩, hrfCB,
              hwsCB⟩ := RCB
            obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩, hrfC8,
              hwsC8⟩ := RC8
            obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
              hrfB0, hwsB0⟩ := RB0
            obtain ⟨hgeB8, hleBF, hlen0, hx10Q, hx11Q, hx13Q, hx7Q,
              htkQ, hwqQ⟩ := long_stem_facts bs inBase d fp off len v rf₀ ws₀
                rfB0 rfC8 rfCB rfB1 rfQ wsB0 wsC8 wsCB wsB1 wsQ L hoff
                hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hdisp hrfC8 hnsingle
                hrfCB hshortb hrfB1 hwsB0 hwsC8 hwsCB hwsB1
            have htr : (bs.getD off 0).toNat - 0xB7 < len := by
              have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
                hlbtr
              rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
                BitVec.toNat_ofNat] at h
              have hnlt : (bs.getD off 0).toNat - 0xB7 < 2 ^ 64 := by
                omega
              rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
              exact h
            have hoff1 : off + 1 < bs.length := by omega
            have haddr1 : rfQ.get .x10 + signExtend12 (1 : BitVec 12)
                = inBase + BitVec.ofNat 64 (off + 1) := by
              rw [se12_1, hx10Q]
              bv_omega
            have hnorw1 : ¬ inRw fp wsQ
                (rfQ.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
              rw [haddr1]
              exact L.not_inRw hlenQ hoff1
            have hstep : (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
                [.LBU .x6 .x10 1]).1 =
                rfQ.set .x6 ((bs.getD (off + 1) 0).zeroExtend 64) := by
              simp only [execBlock_cons, execBlock_nil]
              rw [lbu_ro _ _ _ _ _ _ _ hnorw1, haddr1,
                region_byteAt L.regWf hoff1]
            rw [hstep] at hrfQ
            have hzero : (bs.getD (off + 1) 0).zeroExtend 64 = 0 := by
              have h : rfT.get .x6 = rfT.get .x0 := hlbz
              rw [hrfQ] at h
              simp only [RegFile.get_set_self, RegFile.get_x0, ne_eq,
                reduceCtorEq, not_false_eq_true] at h
              exact h
            have hz : bs.getD (off + 1) 0 = 0 := by
              apply BitVec.eq_of_toNat_eq
              have h := congrArg BitVec.toNat hzero
              rw [toNat_zx] at h
              simpa using h
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
              at hrfT
            refine ⟨?_, ?_, ?_, h3⟩
            · rw [hrfT]
              simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [decStatus_none
                (EvmAsm.EL.RLP.Ref.decodeD_long_bytes_zero d hoff
                  hgeB8 hleBF htr hz)]
            · rw [hrfT]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hrfQ]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hx13Q
            · have e1 : wsR = wsT := by
                rw [hwsT]
                rfl
              have e2 : wsT = wsQ := by
                rw [hwsQ]
                rfl
              rw [e1, e2]
              exact htkQ
          · simp only [Stmt.sp] at TR
            rcases TR with TRsmall | TRrest
            · obtain ⟨rfY, wsY, hlenY, ⟨Rcall, hsmall⟩, hrfR, hwsR⟩ := TRsmall
              obtain ⟨rfP, wsP, hlenP, Rcall2, hrfY, hwsP⟩ := Rcall
              obtain ⟨rf₁, ws₁, A₁, hpreCall, hpre, hpost⟩ := Rcall2
              obtain ⟨rfB1, wsB1, hlenB1, ⟨INNER1, hnlbz⟩,
                hrf₁, hwsB1⟩ := hpreCall
              obtain ⟨rfQ, wsQ, hlenQ, ⟨INNER2, hlbtr⟩,
                hrfB1, hwsQ2⟩ := INNER1
              obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩,
                hrfSB, hwsSB⟩ := INNER2
              obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩,
                hrfCB, hwsCB⟩ := RCB
              obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩,
                hrfC8, hwsC8⟩ := RC8
              obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
                hrfB0, hwsB0⟩ := RB0
              obtain ⟨hgeB8, hleBF, hlen0, hx10Q, hx11Q, hx13Q, hx7Q,
                htkQ, hwqQ⟩ := long_stem_facts bs inBase d fp off len v rf₀ ws₀
                  rfB0 rfC8 rfCB rfSB rfQ wsB0 wsC8 wsCB wsSB wsQ L hoff
                  hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hdisp hrfC8 hnsingle
                  hrfCB hshortb hrfSB hwsB0 hwsC8 hwsCB hwsSB
              have htr : (bs.getD off 0).toNat - 0xB7 < len := by
                have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
                  hlbtr
                rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
                  BitVec.toNat_ofNat] at h
                have hnlt : (bs.getD off 0).toNat - 0xB7 < 2 ^ 64 := by
                  omega
                rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
                exact h
              obtain ⟨hb1ne, hbeV, hbeLt, hx11Y, hx13Y, hx7Y, hx6Y,
                hwsYQ⟩ := long_call_facts bs inBase d fp off len rf₀
                  rfQ rfB1 rf₁ rfP rfY wsQ wsB1 ws₁ wsP wsY A₁ A beS L hoff
                  0xB7 (by omega) (by omega) htr
                  hx10Q hx11Q hx13Q hx7Q hlenQ hbePost hrfB1 hnlbz hrf₁
                  hpost hrfY hwsQ2 hwsB1 hwsP
              have hsmallVal : beVal bs (off + 1)
                  ((bs.getD off 0).toNat - 0xB7) < 0x38 := by
                have h : BitVec.ult (rfY.get .x31) (rfY.get .x6) = true :=
                  hsmall
                rw [hbeV, hx6Y, ult_iff, BitVec.toNat_ofNat] at h
                rw [Nat.mod_eq_of_lt hbeLt] at h
                exact h
              obtain ⟨_, _, _, hAcall⟩ := hbePost rf₁ ws₁ A₁ rfP wsP A hpost
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                at hrfR
              refine ⟨?_, ?_, ?_, hAcall.trans h3⟩
              · rw [hrfR]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [decStatus_none
                  (EvmAsm.EL.RLP.Ref.decodeD_long_bytes_small d hoff
                    hgeB8 hleBF htr hb1ne
                    (by simpa [beVal_eq_winBE] using hsmallVal))]
              · rw [hrfR]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx13Y
              · have e1 : wsR = wsY := by
                  rw [hwsR]
                  rfl
                rw [e1, hwsYQ]
                exact htkQ
            · rcases TRrest with TRok | TRbad
              · obtain ⟨rfF, wsF, hlenF, ⟨Rfit, hfit2⟩, hrfR, hwsR⟩ := TRok
                obtain ⟨rfY, wsY, hlenY, ⟨Rcall, hnsmall⟩,
                  hrfF, hwsF⟩ := Rfit
                obtain ⟨rfP, wsP, hlenP, Rcall2, hrfY, hwsP⟩ := Rcall
                obtain ⟨rf₁, ws₁, A₁, hpreCall, hpre, hpost⟩ := Rcall2
                obtain ⟨rfB1, wsB1, hlenB1, ⟨INNER1, hnlbz⟩,
                  hrf₁, hwsB1⟩ := hpreCall
                obtain ⟨rfQ, wsQ, hlenQ, ⟨INNER2, hlbtr⟩,
                  hrfB1, hwsQ2⟩ := INNER1
                obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩,
                  hrfSB, hwsSB⟩ := INNER2
                obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩,
                  hrfCB, hwsCB⟩ := RCB
                obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩,
                  hrfC8, hwsC8⟩ := RC8
                obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
                  hrfB0, hwsB0⟩ := RB0
                obtain ⟨hgeB8, hleBF, hlen0, hx10Q, hx11Q, hx13Q, hx7Q,
                  htkQ, hwqQ⟩ := long_stem_facts bs inBase d fp off len v rf₀ ws₀
                  rfB0 rfC8 rfCB rfSB rfQ wsB0 wsC8 wsCB wsSB wsQ L hoff
                  hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hdisp hrfC8 hnsingle
                  hrfCB hshortb hrfSB hwsB0 hwsC8 hwsCB hwsSB
                have htr : (bs.getD off 0).toNat - 0xB7 < len := by
                  have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
                    hlbtr
                  rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
                    BitVec.toNat_ofNat] at h
                  have hnlt : (bs.getD off 0).toNat - 0xB7 < 2 ^ 64 := by
                    omega
                  rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
                  exact h
                obtain ⟨hb1ne, hbeV, hbeLt, hx11Y, hx13Y, hx7Y, hx6Y,
                  hwsYQ⟩ := long_call_facts bs inBase d fp off len rf₀
                  rfQ rfB1 rf₁ rfP rfY wsQ wsB1 ws₁ wsP wsY A₁ A beS L hoff
                  0xB7 (by omega) (by omega) htr hx10Q hx11Q hx13Q hx7Q hlenQ hbePost hrfB1
                  hnlbz hrf₁ hpost hrfY hwsQ2 hwsB1 hwsP
                have hbigVal : 0x38 ≤ beVal bs (off + 1)
                    ((bs.getD off 0).toNat - 0xB7) := by
                  have h : ¬ (BitVec.ult (rfY.get .x31) (rfY.get .x6) = true) :=
                    hnsmall
                  rw [hbeV, hx6Y, ult_iff, BitVec.toNat_ofNat] at h
                  rw [Nat.mod_eq_of_lt hbeLt] at h
                  exact Nat.le_of_not_gt h
                simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                  at hrfF hrfR
                have hx6F : rfF.get .x6 = BitVec.ofNat 64
                    (len - 1 - ((bs.getD off 0).toNat - 0xB7)) := by
                  rw [hrfF]
                  try simp only [
                    RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  try rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ Reg.x6)]
                  rw [show rfY.get .x11 = BitVec.ofNat 64 len from hx11Y,
                    hx7Y,
                    se12_n1]
                  bv_omega
                have hx31F : rfF.get .x31 = BitVec.ofNat 64
                    (beVal bs (off + 1) ((bs.getD off 0).toNat - 0xB7)) := by
                  rw [hrfF]
                  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  exact hbeV
                have hval : beVal bs (off + 1)
                    ((bs.getD off 0).toNat - 0xB7) =
                    len - 1 - ((bs.getD off 0).toNat - 0xB7) := by
                  have h : rfF.get .x31 = rfF.get .x6 := hfit2
                  rw [hx31F, hx6F] at h
                  have h' := congrArg BitVec.toNat h
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h'
                  omega
                have hfitVal : len = 1 + ((bs.getD off 0).toNat - 0xB7)
                    + beVal bs (off + 1)
                      ((bs.getD off 0).toNat - 0xB7) := by
                  rw [hval]
                  omega
                have hx13F : rfF.get .x13 = fp := by
                  rw [hrfF]
                  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  exact hx13Y
                obtain ⟨_, _, _, hAcall⟩ := hbePost rf₁ ws₁ A₁ rfP wsP A hpost
                refine ⟨?_, ?_, ?_, hAcall.trans h3⟩
                · rw [hrfR]
                  simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  rw [decStatus_some
                    (EvmAsm.EL.RLP.Ref.decodeD_long_bytes_ok d hoff
                      hgeB8 hleBF htr hb1ne
                      (by simpa [beVal_eq_winBE] using hbigVal)
                      (by simpa [beVal_eq_winBE] using hfitVal))]
                · rw [hrfR]
                  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  exact hx13F
                · have e1 : wsR = wsF := by
                    rw [hwsR]
                    rfl
                  have e2 : wsF = wsY := by
                    rw [hwsF]
                    rfl
                  rw [e1, e2, hwsYQ]
                  exact htkQ
              · obtain ⟨rfF, wsF, hlenF, ⟨Rfit, hfit2⟩, hrfR, hwsR⟩ := TRbad
                obtain ⟨rfY, wsY, hlenY, ⟨Rcall, hnsmall⟩,
                  hrfF, hwsF⟩ := Rfit
                obtain ⟨rfP, wsP, hlenP, Rcall2, hrfY, hwsP⟩ := Rcall
                obtain ⟨rf₁, ws₁, A₁, hpreCall, hpre, hpost⟩ := Rcall2
                obtain ⟨rfB1, wsB1, hlenB1, ⟨INNER1, hnlbz⟩,
                  hrf₁, hwsB1⟩ := hpreCall
                obtain ⟨rfQ, wsQ, hlenQ, ⟨INNER2, hlbtr⟩,
                  hrfB1, hwsQ2⟩ := INNER1
                obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩,
                  hrfSB, hwsSB⟩ := INNER2
                obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩,
                  hrfCB, hwsCB⟩ := RCB
                obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩,
                  hrfC8, hwsC8⟩ := RC8
                obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
                  hrfB0, hwsB0⟩ := RB0
                obtain ⟨hgeB8, hleBF, hlen0, hx10Q, hx11Q, hx13Q, hx7Q,
                  htkQ, hwqQ⟩ := long_stem_facts bs inBase d fp off len v rf₀ ws₀
                  rfB0 rfC8 rfCB rfSB rfQ wsB0 wsC8 wsCB wsSB wsQ L hoff
                  hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hdisp hrfC8 hnsingle
                  hrfCB hshortb hrfSB hwsB0 hwsC8 hwsCB hwsSB
                have htr : (bs.getD off 0).toNat - 0xB7 < len := by
                  have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
                    hlbtr
                  rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
                    BitVec.toNat_ofNat] at h
                  have hnlt : (bs.getD off 0).toNat - 0xB7 < 2 ^ 64 := by
                    omega
                  rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
                  exact h
                obtain ⟨hb1ne, hbeV, hbeLt, hx11Y, hx13Y, hx7Y, hx6Y,
                  hwsYQ⟩ := long_call_facts bs inBase d fp off len rf₀
                  rfQ rfB1 rf₁ rfP rfY wsQ wsB1 ws₁ wsP wsY A₁ A beS L hoff
                  0xB7 (by omega) (by omega) htr hx10Q hx11Q hx13Q hx7Q hlenQ hbePost hrfB1
                  hnlbz hrf₁ hpost hrfY hwsQ2 hwsB1 hwsP
                have hbigVal : 0x38 ≤ beVal bs (off + 1)
                    ((bs.getD off 0).toNat - 0xB7) := by
                  have h : ¬ (BitVec.ult (rfY.get .x31) (rfY.get .x6) = true) :=
                    hnsmall
                  rw [hbeV, hx6Y, ult_iff, BitVec.toNat_ofNat] at h
                  rw [Nat.mod_eq_of_lt hbeLt] at h
                  exact Nat.le_of_not_gt h
                simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                  at hrfF hrfR
                have hx6F : rfF.get .x6 = BitVec.ofNat 64
                    (len - 1 - ((bs.getD off 0).toNat - 0xB7)) := by
                  rw [hrfF]
                  try simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  try rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ Reg.x6)]
                  rw [show rfY.get .x11 = BitVec.ofNat 64 len from hx11Y,
                    show rfY.get .x7 = BitVec.ofNat 64
                      ((bs.getD off 0).toNat - 0xB7) from hx7Y,
                    se12_n1]
                  bv_omega
                have hx31F : rfF.get .x31 = BitVec.ofNat 64
                    (beVal bs (off + 1) ((bs.getD off 0).toNat - 0xB7)) := by
                  rw [hrfF]
                  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  exact hbeV
                have hx13F : rfF.get .x13 = fp := by
                  rw [hrfF]
                  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  exact hx13Y
                have hbadVal : len ≠ 1 + ((bs.getD off 0).toNat - 0xB7)
                    + beVal bs (off + 1)
                      ((bs.getD off 0).toNat - 0xB7) := by
                  intro hfit
                  apply hfit2
                  show rfF.get .x31 = rfF.get .x6
                  rw [hx31F, hx6F]
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
                  omega
                obtain ⟨_, _, _, hAcall⟩ := hbePost rf₁ ws₁ A₁ rfP wsP A hpost
                refine ⟨?_, ?_, ?_, hAcall.trans h3⟩
                · rw [hrfR]
                  simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  rw [decStatus_none
                    (EvmAsm.EL.RLP.Ref.decodeD_long_bytes_badlen d hoff
                      hgeB8 hleBF htr hb1ne
                      (by simpa [beVal_eq_winBE] using hbigVal)
                      (by simpa [beVal_eq_winBE] using hbadVal))]
                · rw [hrfR]
                  simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                  exact hx13F
                · have e1 : wsR = wsF := by
                    rw [hwsR]
                    rfl
                  have e2 : wsF = wsY := by
                    rw [hwsF]
                    rfl
                  rw [e1, e2, hwsYQ]
                  exact htkQ
        · have RCB := INNER2.1
          have hshortb := INNER2.2
          obtain ⟨rfCB, wsCB, hlenCB, ⟨RC8, hnsingle⟩, hrfCB,
            hwsCB⟩ := RCB
          obtain ⟨rfC8, wsC8, hlenC8, ⟨RB0, hdisp⟩, hrfC8,
            hwsC8⟩ := RC8
          rcases RB0 with ⟨rfB0, RB0⟩
          rcases RB0 with ⟨wsB0, RB0⟩
          rcases RB0 with ⟨hlenB0, RB0⟩
          rcases RB0 with ⟨hstateB0, RB0⟩
          rcases hstateB0 with ⟨hfieldsB0, hne⟩
          rcases hfieldsB0 with ⟨h1, h2, h3⟩
          rcases RB0 with ⟨hrfB0, hwsB0⟩
          obtain ⟨hgeB8, hleBF, hlen0, hx10Q, hx11Q, hx13Q, hx7Q,
            htkQ, hwqQ⟩ := long_stem_facts bs inBase d fp off len v rf₀ ws₀
              rfB0 rfC8 rfCB rfB1 rfW wsB0 wsC8 wsCB wsB1 wsW L hoff
              hx10 hx11 hx13 hlenB0 h1 h2 hne hrfB0 hdisp hrfC8 hnsingle
              hrfCB hshortb hrfB1 hwsB0 hwsC8 hwsCB hwsB1
          have htr : len ≤ (bs.getD off 0).toNat - 0xB7 := by
            have h : ¬ (BitVec.ult (rfW.get .x7) (rfW.get .x11) = true) :=
              hlbtr
            rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat] at h
            omega
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            at hrfW
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hrfW]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [decStatus_none
              (EvmAsm.EL.RLP.Ref.decodeD_long_bytes_trunc d hoff hlen0
                hgeB8 hleBF htr)]
          · rw [hrfW]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hx13Q
          · have hwsRW : wsR = wsW := by
              rw [hwsW]
              rfl
            rw [hwsRW]
            exact htkQ
          · exact h3
  · simp only [listArm, Stmt.sp] at LI
    rcases LI with hgo | hnogo
    · rcases hgo with ⟨rfL, wsL, hlenL, hpreL, hrfL, hwsL⟩
      rcases hpreL with ⟨rfH, wsH, AH, hH, hCall⟩
      rcases hH with ⟨rfB, wsB, hlenB, hHead⟩
      rcases hHead with ⟨hHead, hwsH⟩
      rcases hHead with ⟨hcase, hrfH⟩
      rcases hcase with hbudget | hhead
      · rcases hbudget with ⟨rfX, wsX, hlenX, hpreX, hrfB', hwsB'⟩
        have hx14B : rfB.get .x14 = (1 : Word) := by
          rw [hrfB']
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
            RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
        have hx14B0 : rfB.get .x14 = (0 : Word) := hrfH
        rw [hx14B] at hx14B0
        simp at hx14B0
      · rcases hhead with hshort | hlong
        · simp only [listShortHdr, Stmt.sp] at hshort
          rcases hshort with ⟨rsl, ssl, hsl, hrest⟩
          rcases hrest with ⟨hleft, hrfBshort, hwsBshort⟩
          rcases hleft with ⟨hpre, hfitCond⟩
          rcases hpre with ⟨rpre, spre, hpreLen, hpreRest⟩
          rcases hpreRest with ⟨hpreRest, hrsl, hsSL⟩
          rcases hpreRest with ⟨hpreInit, hdisp⟩
          rcases hpreInit with ⟨r0, s0, h0, hinitRest⟩
          rcases hinitRest with ⟨hinitRest, hrpre, hsPre⟩
          rcases hinitRest with ⟨hinitRest, hbud⟩
          rcases hinitRest with ⟨hentry, hnotdisp⟩
          rcases hentry with ⟨rE, sE, hE, hReach, hr0, hs0⟩
          rcases hReach with ⟨⟨hrE, hsE, hAE⟩, hneE⟩
          rw [hrE] at hneE
          have hlen0 : 0 < len := by
            rcases Nat.eq_zero_or_pos len with hzero | hpos
            · exact absurd (by rw [hx11, hzero]; simp :
                rf₀.get .x11 = rf₀.get .x0) hneE
            · exact hpos
          have hoffb : off < bs.length :=
            Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlen0) hoff
          rw [hrE, hsE] at hr0 hs0
          have hset : (setBytes ws₀ 0 (dwordBytes v)).length = 40 * d + 8 := by
            rw [← hsE]
            exact hE
          rw [b0_engine bs inBase fp _ L rf₀ (setBytes ws₀ 0 (dwordBytes v))
            hset off hx10 hoffb] at hr0 hs0
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            at hrpre hsPre hrsl hsSL hrfBshort hwsBshort hwsH hrfL hwsL hs0
          have hv5 : r0.get .x5 = (bs.getD off 0).zeroExtend 64 := by
            rw [hr0]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
          have hv6 : r0.get .x6 = (0xC0 : Word) := by
            rw [hr0]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
          have hgeC0 : 0xC0 ≤ (bs.getD off 0).toNat := by
            have h : ¬ (BitVec.ult (r0.get .x5) (r0.get .x6) = true) :=
              hnotdisp
            rw [hv5, hv6, ult_iff, toNat_zx] at h
            have hc : ((0xC0 : Word)).toNat = 0xC0 := rfl
            omega
          have hv5pre : rpre.get .x5 = (bs.getD off 0).zeroExtend 64 := by
            rw [hrpre]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hv5
          have hv6pre : rpre.get .x6 = (0xF8 : Word) := by
            rw [hrpre]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
          have hleF7 : (bs.getD off 0).toNat ≤ 0xF7 := by
            have h : BitVec.ult (rpre.get .x5) (rpre.get .x6) = true := hdisp
            rw [hv5pre, hv6pre, ult_iff, toNat_zx] at h
            have hc : ((0xF8 : Word)).toNat = 0xF8 := rfl
            omega
          have hx7sl : rsl.get .x7 = BitVec.ofNat 64
              ((bs.getD off 0).toNat - 0xC0) := by
            rw [hrsl]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hv5pre, se12_nC0]
            bv_omega
          have hx6sl : rsl.get .x6 = BitVec.ofNat 64
              ((bs.getD off 0).toNat - 0xC0) + 1 := by
            rw [hrsl]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hv5pre, se12_nC0, se12_1]
            bv_omega
          have hfitVal : len = 1 + ((bs.getD off 0).toNat - 0xC0) := by
            have h : rsl.get .x6 = rsl.get .x11 := hfitCond
            have hx11sl : rsl.get .x11 = BitVec.ofNat 64 len := by
              rw [hrsl]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hrpre]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              rw [hr0]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hx11
            rw [hx6sl, hx11sl] at h
            have h' := congrArg BitVec.toNat h
            rw [BitVec.toNat_add, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat] at h'
            have h1n : ((1 : Word)).toNat = 1 := rfl
            omega
          have hx10rsl : rsl.get .x10 = inBase + BitVec.ofNat 64 off := by
            rw [hrsl]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrpre]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hr0]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hx10
          have hx15B : rfB.get .x15 = inBase + BitVec.ofNat 64 (off + 1) := by
            rw [hrfBshort]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hx10rsl, se12_1]
            bv_omega
          have hx16B : rfB.get .x16 = inBase + BitVec.ofNat 64 (off + len) := by
            rw [hrfBshort]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hx10rsl, hx7sl, se12_1]
            bv_omega
          have hps : pStartOf inBase rfH = off + 1 := by
            unfold pStartOf
            rw [hwsH.1]
            simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hx15B, idxOf_add inBase (off + 1) (by omega) (by omega)]
          have hpe : pEndOf inBase rfH = off + len := by
            unfold pEndOf
            rw [hwsH.1]
            simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hx16B, idxOf_add inBase (off + len) (by omega) (by omega)]
          have hdpos : 1 ≤ d := by
            have hx12r0 : r0.get .x12 = BitVec.ofNat 64 d := by
              rw [hr0]
              simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                not_false_eq_true]
              exact hx12
            rcases Nat.eq_zero_or_pos d with hzero | hpos
            · apply False.elim
              apply hbud
              change r0.get .x12 = r0.get .x0
              rw [hx12r0, hzero]
              simp
            · exact hpos
          rcases hCall with ⟨hpreC, hpostC⟩
          obtain ⟨hstat, hfp, hslot, hAc⟩ :=
            hitPost hdpos rfH wsH AH rfL wsL A hpostC
          have hJ := EvmAsm.EL.RLP.Ref.decodeD_short_list_items (d - 1)
            hoff hgeC0 hleF7 hfitVal
          have hstatusEq : decStatus bs off len d =
              itemsStatus bs (pStartOf inBase rfH)
                (pEndOf inBase rfH - pStartOf inBase rfH) (d - 1) := by
            unfold decStatus itemsStatus
            rw [hps, hpe]
            have hlenPayload : off + len - (off + 1) = len - 1 := by omega
            rw [hlenPayload]
            have hdec : decodeD d (EvmAsm.EL.RLP.Ref.win bs off len) =
                Option.map EL.RLP.RLPItem.list
                  (decodeJoinedEncodingsD (d - 1)
                    (EvmAsm.EL.RLP.Ref.win bs (off + 1) (len - 1))) := by
              rw [show d = d - 1 + 1 by omega]
              exact hJ
            rw [hdec]
            cases hq : EvmAsm.EL.RLP.Ref.decodeJoinedEncodingsD (d - 1)
                (EvmAsm.EL.RLP.Ref.win bs (off + 1) (len - 1)) <;>
              simp
          have hrfR14 : rfR.get .x14 = rfL.get .x10 := by
            rw [hrfL]
            simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true]
          have hrfR13 : rfR.get .x13 = fp := by
            rw [hrfL]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hfp, se12_n8]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
            bv_omega
          have hwsR' : wsR = wsL := by
            rw [hwsL]
          have hstk : wsR.take 8 = dwordBytes v := by
            rw [hwsR', hslot]
            rw [hwsH.2, hwsBshort, hsSL, hsPre, hs0]
            have hs := setBytes_slot ws₀ (dwordBytes v) 0
              (by
                rw [length_dwordBytes]
                have hl : sE.length = 40 * d + 8 := hE
                rw [hsE, length_setBytes] at hl
                omega)
            rw [List.drop_zero, length_dwordBytes] at hs
            exact hs
          refine ⟨?_, hrfR13, hstk, hAc.trans hAE⟩
          rw [hrfR14, hstat, hstatusEq]
          all_goals
            rename_i hfail
            rcases hfail with ⟨rfF, wsF, hlenF, hpreF, hrfBF, hwsBF⟩
            have hx14B1 : rfB.get .x14 = (1 : Word) := by
              rw [hrfBF]
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
            have hx14B0 : rfB.get .x14 = (0 : Word) := hrfH
            rw [hx14B1] at hx14B0
            simp at hx14B0
        · simp only [listLongHdr, Stmt.sp] at hlong
          rcases hlong with TR | ⟨rfW, wsW, hlenW,
            ⟨⟨rfB1, wsB1, hlenB1, INNER2, hrfB1, hwsB1⟩, hltr⟩,
            hrfW, hwsW⟩
          · rcases TR with TR | TR
            · obtain ⟨rfT, wsT, hlenT, ⟨INNER1, hlbz⟩, hrfT, hwsT⟩ := TR
              have hx14B1 : rfB.get .x14 = (1 : Word) := by
                rw [hrfT]
                simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                  RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
              have hx14B0 : rfB.get .x14 = (0 : Word) := hrfH
              rw [hx14B1] at hx14B0
              simp at hx14B0
              /-
              obtain ⟨rfQ, wsQ, hlenQ, hrestQ, hrfQ, hwsQ⟩ := INNER1
              rcases hrestQ with ⟨hrest, hlbtr⟩
              obtain ⟨rfCB, wsCB, hlenCB, hrestCB, hrfCB, hwsCB⟩ := hrest
              rcases hrestCB with ⟨hrestB1, hshortb⟩
              obtain ⟨rfB1, wsB1, hlenB1, hrestB1, hrfB1,
                hwsB1⟩ := hrestB1
              rcases hrestB1 with ⟨⟨RB0, hshortB1⟩, hbud⟩
              obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
                hrfB0, hwsB0⟩ := RB0
              have hlen0 : 0 < len := by
                rcases Nat.eq_zero_or_pos len with hzero | hpos
                · rw [h1] at hne
                  exact absurd (by rw [hx11, hzero]; simp :
                    rf₀.get .x11 = rf₀.get .x0) hne
                · exact hpos
              have hoffb : off < bs.length := by omega
              rw [h1] at hrfB0
              rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb]
                at hrfB0
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                at hrfB1 hrfCB hwsB1 hwsCB hrfT
              have hv5B1 : rfB1.get .x5 =
                  (bs.getD off 0).zeroExtend 64 := by
                rw [hrfB0]
                simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
                  reduceCtorEq, not_false_eq_true]
              have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
                have h : ¬ (BitVec.ult (rfCB.get .x5) (rfCB.get .x6) = true) :=
                  hshortb
                rw [hrfB1] at h
                simp only [execBlock_cons, execBlock_nil, execInstrRF,
                  aluSem, RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
                  reduceCtorEq, not_false_eq_true] at h
                rw [hv5B1, ult_iff, EvmAsm.Rv64.RLP.toNat_byte_zeroExtend,
                  BitVec.toNat_ofNat] at h
                omega
              have hx10Q : rfQ.get .x10 = inBase + BitVec.ofNat 64 off := by
                rw [hrfCB]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB1]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB0]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx10
              have hx11Q : rfQ.get .x11 = BitVec.ofNat 64 len := by
                rw [hrfCB]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB1]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB0]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx11
              have hx13Q : rfQ.get .x13 = fp := by
                rw [hrfCB]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB1]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB0]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx13
              have hx7Q : rfQ.get .x7 = BitVec.ofNat 64
                  ((bs.getD off 0).toNat - 0xF7) := by
                rw [hrfCB]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfB1]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hv5B1, se12_nF7]
                bv_omega
              have htkQ : wsQ.take 8 = dwordBytes v := by
                have hwsQ' : wsQ = wsB0 := by
                  rw [hwsCB, hwsB1, hwsB0, h2]
                  rfl
                rw [hwsQ', h2]
                have hws0 : ws₀.length = 40 * d + 8 := by
                  have hh := hlenB0
                  rw [h2, length_setBytes] at hh
                  exact hh
                have hs := setBytes_slot ws₀ (dwordBytes v) 0
                  (by rw [length_dwordBytes, hws0]; omega)
                rw [List.drop_zero, length_dwordBytes] at hs
                exact hs
              have htr : (bs.getD off 0).toNat - 0xF7 < len := by
                have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
                  hlbtr
                rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
                  BitVec.toNat_ofNat] at h
                have hnlt : (bs.getD off 0).toNat - 0xF7 < 2 ^ 64 := by
                  omega
                rw [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hlen64] at h
                exact h
              /-
              have hoff1 : off + 1 < bs.length := by omega
              have haddr1 : rfQ.get .x10 + signExtend12 (1 : BitVec 12)
                  = inBase + BitVec.ofNat 64 (off + 1) := by
                rw [se12_1, hx10Q]
                bv_omega
              have hnorw1 : ¬ inRw fp wsQ
                  (rfQ.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
                rw [haddr1]
                exact L.not_inRw hlenQ hoff1
              have hstep : (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
                  [.LBU .x6 .x10 1]).1 =
                  rfQ.set .x6 ((bs.getD (off + 1) 0).zeroExtend 64) := by
                simp only [execBlock_cons, execBlock_nil]
                rw [lbu_ro _ _ _ _ _ _ _ hnorw1, haddr1,
                  region_byteAt L.regWf hoff1]
              rw [hstep] at hrfQ
              have hzero : (bs.getD (off + 1) 0).zeroExtend 64 = 0 := by
                have h : rfT.get .x6 = rfT.get .x0 := hlbz
                rw [hrfQ] at h
                simp only [RegFile.get_set_self, RegFile.get_x0, ne_eq,
                  reduceCtorEq, not_false_eq_true] at h
                exact h
              have hz : bs.getD (off + 1) 0 = 0 := by
                apply BitVec.eq_of_toNat_eq
                have h := congrArg BitVec.toNat hzero
                rw [toNat_zx] at h
                simpa using h
              refine ⟨?_, ?_, ?_, h3⟩
              · rw [hrfT]
                simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [decStatus_none
                  (EvmAsm.EL.RLP.Ref.decodeD_long_list_zero d hoff
                    hgeF8 htr hz)]
              · rw [hrfT]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                rw [hrfQ]
                simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                  not_false_eq_true]
                exact hx13Q
              · have e1 : wsR = wsT := by
                  rw [hwsT]
                  rfl
                have e2 : wsT = wsQ := by
                  rw [hwsQ]
                  rfl
                rw [e1, e2]
              exact htkQ -/
            -/
            · rcases TR with TRsmall | TRrest
              · obtain ⟨rfX, wsX, hlenX, hrestX, hrfX, hwsX⟩ := TRsmall
                have hx14B1 : rfB.get .x14 = (1 : Word) := by
                  rw [hrfX]
                  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                    RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
                have hx14B0 : rfB.get .x14 = (0 : Word) := hrfH
                rw [hx14B1] at hx14B0
                simp at hx14B0
              · rcases TRrest with TRok | TRbad
                · obtain ⟨rfF, wsF, hlenF, ⟨Rfit, hfit2⟩, hrfR, hwsR⟩ := TRok
                  obtain ⟨rfY, wsY, hlenY, ⟨Rcall, hnsmall⟩,
                    hrfF, hwsF⟩ := Rfit
                  obtain ⟨rfP, wsP, hlenP, Rcall2, hrfY, hwsP⟩ := Rcall
                  obtain ⟨rf₁, ws₁, A₁, hpreCall, hpre, hpost⟩ := Rcall2
                  obtain ⟨rfB1, wsB1, hlenB1, ⟨INNER1, hnlbz⟩,
                    hrf₁, hwsB1⟩ := hpreCall
                  obtain ⟨rfQ, wsQ, hlenQ, ⟨INNER2, hlbtr⟩,
                    hrfB1, hwsQ2⟩ := INNER1
                  obtain ⟨rfSB, wsSB, hlenSB, ⟨RCB, hshortb⟩,
                    hrfSB, hwsSB⟩ := INNER2
                  obtain ⟨rfCB, wsCB, hlenCB, hrestCB,
                    hrfCB, hwsCB⟩ := RCB
                  rcases hrestCB with ⟨⟨RB0, hlist0⟩, hbud⟩
                  obtain ⟨rfB0, wsB0, hlenB0, ⟨⟨h1, h2, h3⟩, hne⟩,
                    hrfB0, hwsB0⟩ := RB0
                  have hlen0 : 0 < len := by
                    rcases Nat.eq_zero_or_pos len with hzero | hpos
                    · rw [h1] at hne
                      exact absurd (by rw [hx11, hzero]; simp :
                        rf₀.get .x11 = rf₀.get .x0) hne
                    · exact hpos
                  have hoffb : off < bs.length := by omega
                  rw [h1] at hrfB0
                  rw [b0_engine bs inBase fp _ L rf₀ wsB0 hlenB0 off hx10 hoffb]
                    at hrfB0
                  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
                    at hrfCB hrfSB hrf₁ hrfY hrfF hrfR hwsH hrfL hwsL
                      hwsR hwsF hwsP hwsB1 hwsQ2 hwsSB hwsCB hwsB0
                  have hv5CB : rfCB.get .x5 =
                      (bs.getD off 0).zeroExtend 64 := by
                    rw [hrfB0]
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true]
                  have hgeF8 : 0xF8 ≤ (bs.getD off 0).toNat := by
                    have h : ¬ (BitVec.ult (rfSB.get .x5) (rfSB.get .x6) = true) :=
                      hshortb
                    rw [hrfCB] at h
                    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
                      reduceCtorEq, not_false_eq_true] at h
                    rw [hv5CB, ult_iff, toNat_zx] at h
                    have hc : ((0xF8 : Word)).toNat = 0xF8 := rfl
                    omega
                  have hx7Q : rfQ.get .x7 = BitVec.ofNat 64
                      ((bs.getD off 0).toNat - 0xF7) := by
                    rw [hrfSB]
                    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfCB]
                    simp only [RegFile.get_set_ne,
                      ne_eq, reduceCtorEq, not_false_eq_true]
                    rw [hv5CB, se12_nF7]
                    bv_omega
                  have hx11Q : rfQ.get .x11 = BitVec.ofNat 64 len := by
                    rw [hrfSB]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfCB]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfB0]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx11
                  have htr : (bs.getD off 0).toNat - 0xF7 < len := by
                    have h : BitVec.ult (rfQ.get .x7) (rfQ.get .x11) = true :=
                      hlbtr
                    rw [hx7Q, hx11Q, ult_iff, BitVec.toNat_ofNat,
                      BitVec.toNat_ofNat] at h
                    omega
                  have hx10Q : rfQ.get .x10 =
                      inBase + BitVec.ofNat 64 off := by
                    rw [hrfSB]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfCB]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfB0]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx10
                  have hoff1 : off + 1 < bs.length := by omega
                  have haddr1 : rfQ.get .x10 +
                      signExtend12 (1 : BitVec 12) =
                      inBase + BitVec.ofNat 64 (off + 1) := by
                    rw [hx10Q, se12_1]
                    bv_omega
                  have hnorw1 : ¬ inRw fp wsQ
                      (rfQ.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
                    rw [haddr1]
                    exact L.not_inRw hlenQ hoff1
                  rw [show (execBlock ⟨inBase, bs⟩ fp rfQ wsQ
                      [.LBU .x6 .x10 1]).1 =
                      rfQ.set .x6 ((bs.getD (off + 1) 0).zeroExtend 64) by
                    simp only [execBlock_cons, execBlock_nil]
                    rw [lbu_ro _ _ _ _ _ _ _ hnorw1, haddr1,
                      region_byteAt L.regWf hoff1]] at hrfB1
                  have hb1ne : bs.getD (off + 1) 0 ≠ 0 := by
                    intro hzero
                    apply hnlbz
                    show rfB1.get .x6 = rfB1.get .x0
                    rw [hrfB1]
                    simp only [RegFile.get_set_self, RegFile.get_x0,
                      ne_eq, reduceCtorEq, not_false_eq_true]
                    rw [hzero]
                    rfl
                  have hx29 : rf₁.get .x29 =
                      inBase + BitVec.ofNat 64 (off + 1) := by
                    rw [hrf₁]
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true]
                    rw [hrfB1]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    -- The address is unchanged by the second-byte load.
                    rw [show rfQ.get .x10 =
                        inBase + BitVec.ofNat 64 off by
                          rw [hrfSB]
                          simp only [RegFile.get_set_ne, ne_eq,
                            reduceCtorEq, not_false_eq_true]
                          rw [hrfCB]
                          simp only [RegFile.get_set_ne, ne_eq,
                            reduceCtorEq, not_false_eq_true]
                          rw [hrfB0]
                          simp only [RegFile.get_set_ne, ne_eq,
                            reduceCtorEq, not_false_eq_true]
                          exact hx10, se12_1]
                    bv_omega
                  have hx30 : rf₁.get .x30 = BitVec.ofNat 64
                      ((bs.getD off 0).toNat - 0xF7) := by
                    rw [hrf₁]
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true]
                    rw [hrfB1]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx7Q
                  obtain ⟨hx31P, hpins, hwsPeq, hAP⟩ :=
                    hbePost rf₁ ws₁ A₁ rfP wsP AH hpost
                  have hbeV : rfP.get .x31 = BitVec.ofNat 64
                      (beVal bs (off + 1)
                        ((bs.getD off 0).toNat - 0xF7)) := by
                    rw [hx31P, hx29, hx30,
                      idxOf_add inBase (off + 1) (by omega) (by omega),
                      BitVec.toNat_ofNat]
                    congr 2
                    omega
                  have hbeLt : beVal bs (off + 1)
                      ((bs.getD off 0).toNat - 0xF7) < 2 ^ 64 := by
                    unfold beVal
                    have hh := EvmAsm.EL.RLP.Nat.fromBytesBE_lt
                      ((bs.drop (off + 1)).take
                        ((bs.getD off 0).toNat - 0xF7))
                    have hlen : ((bs.drop (off + 1)).take
                        ((bs.getD off 0).toNat - 0xF7)).length ≤
                        ((bs.getD off 0).toNat - 0xF7) := by
                      rw [List.length_take]
                      omega
                    have hpow : 256 ^ (((bs.drop (off + 1)).take
                        ((bs.getD off 0).toNat - 0xF7)).length) ≤
                        256 ^ 8 := by
                      exact Nat.pow_le_pow_right (by omega) (by omega)
                    exact lt_of_lt_of_le hh hpow
                  have hbigVal : 0x38 ≤ beVal bs (off + 1)
                      ((bs.getD off 0).toNat - 0xF7) := by
                    have h : ¬ (BitVec.ult (rfY.get .x31) (rfY.get .x6) = true) :=
                      hnsmall
                    rw [hrfY] at h
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true] at h
                    rw [hbeV, ult_iff, BitVec.toNat_ofNat] at h
                    rw [Nat.mod_eq_of_lt hbeLt] at h
                    exact Nat.le_of_not_gt h
                  have hx7Y : rfY.get .x7 = BitVec.ofNat 64
                      ((bs.getD off 0).toNat - 0xF7) := by
                    rw [hrfY]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hpins .x7 (by decide) (by decide) (by decide)
                      (by decide)]
                    rw [hrf₁]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfB1]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx7Q
                  have hx31Y : rfY.get .x31 = BitVec.ofNat 64
                      (beVal bs (off + 1)
                        ((bs.getD off 0).toNat - 0xF7)) := by
                    rw [hrfY]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hbeV
                  have hx6F : rfF.get .x6 = BitVec.ofNat 64
                      (len - 1 - ((bs.getD off 0).toNat - 0xF7)) := by
                    rw [hrfF]
                    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ Reg.x6)]
                    have hx11Y : rfY.get .x11 = BitVec.ofNat 64 len := by
                      rw [hrfY]
                      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                        not_false_eq_true]
                      rw [hpins .x11 (by decide) (by decide) (by decide)
                        (by decide)]
                      rw [hrf₁]
                      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                        not_false_eq_true]
                      rw [hrfB1]
                      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                        not_false_eq_true]
                      exact hx11Q
                    rw [hx11Y, hx7Y, se12_n1]
                    bv_omega
                  have hx31F : rfF.get .x31 = BitVec.ofNat 64
                      (beVal bs (off + 1)
                        ((bs.getD off 0).toNat - 0xF7)) := by
                    rw [hrfF]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx31Y
                  have hfitVal : len = 1 + ((bs.getD off 0).toNat - 0xF7) +
                      beVal bs (off + 1) ((bs.getD off 0).toNat - 0xF7) := by
                    have h : rfF.get .x31 = rfF.get .x6 := hfit2
                    rw [hx31F, hx6F] at h
                    have hh := congrArg BitVec.toNat h
                    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hh
                    omega
                  have hJ := EvmAsm.EL.RLP.Ref.decodeD_long_list_items
                    (d - 1) hoff hgeF8 htr hb1ne
                    (by simpa [beVal_eq_winBE] using hbigVal)
                    (by simpa [beVal_eq_winBE] using hfitVal)
                  obtain ⟨hpreItems, hpostItems⟩ := hCall
                  have hdpos : 1 ≤ d := by
                    have hx12CB : rfCB.get .x12 = BitVec.ofNat 64 d := by
                      rw [hrfB0]
                      simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                        not_false_eq_true]
                      exact hx12
                    rcases Nat.eq_zero_or_pos d with hzero | hpos
                    · apply False.elim
                      apply hbud
                      change rfCB.get .x12 = rfCB.get .x0
                      rw [hx12CB, hzero]
                      simp
                    · exact hpos
                  obtain ⟨hstat, hfp, hslot, hAc⟩ :=
                    hitPost hdpos rfH wsH AH rfL wsL A hpostItems
                  have hx10Y : rfY.get .x10 = inBase + BitVec.ofNat 64 off := by
                    rw [hrfY]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hpins .x10 (by decide) (by decide) (by decide)
                      (by decide)]
                    rw [hrf₁]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hrfB1]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx10Q
                  have hx10F : rfF.get .x10 = inBase + BitVec.ofNat 64 off := by
                    rw [hrfF]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx10Y
                  have hx7F : rfF.get .x7 = BitVec.ofNat 64
                      ((bs.getD off 0).toNat - 0xF7) := by
                    rw [hrfF]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    exact hx7Y
                  have hx15B : rfB.get .x15 = inBase + BitVec.ofNat 64
                      (off + 1 + ((bs.getD off 0).toNat - 0xF7)) := by
                    have h := congrArg (fun r : RegFile => r.get .x15) hrfR
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true] at h
                    rw [h]
                    rw [hx10F, hx7F, se12_1]
                    change inBase + BitVec.ofNat 64 off + BitVec.ofNat 64 1 +
                      BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) = _
                    rw [addr_add inBase off 1,
                      addr_add inBase (off + 1)
                        ((bs.getD off 0).toNat - 0xF7)]
                  have hx16B : rfB.get .x16 = inBase + BitVec.ofNat 64
                      (off + len) := by
                    have h := congrArg (fun r : RegFile => r.get .x16) hrfR
                    simp only [RegFile.get_set_ne, RegFile.get_set_self,
                      ne_eq, reduceCtorEq, not_false_eq_true] at h
                    rw [h]
                    rw [hx10F, hx7F, hx31F, se12_1]
                    change inBase + BitVec.ofNat 64 off + BitVec.ofNat 64 1 +
                      BitVec.ofNat 64 ((bs.getD off 0).toNat - 0xF7) +
                      BitVec.ofNat 64 (beVal bs (off + 1)
                        ((bs.getD off 0).toNat - 0xF7)) = _
                    rw [addr_add inBase off 1,
                      addr_add inBase (off + 1)
                        ((bs.getD off 0).toNat - 0xF7),
                      addr_add inBase
                        (off + 1 + ((bs.getD off 0).toNat - 0xF7))
                        (beVal bs (off + 1)
                          ((bs.getD off 0).toNat - 0xF7)),
                      hfitVal]
                    simp only [Nat.add_assoc]
                  have hps : pStartOf inBase rfH = off + 1 +
                      ((bs.getD off 0).toNat - 0xF7) := by
                    unfold pStartOf
                    rw [hwsH.1]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hx15B, idxOf_add inBase _ (by omega) (by omega)]
                  have hpe : pEndOf inBase rfH = off + len := by
                    unfold pEndOf
                    rw [hwsH.1]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hx16B, idxOf_add inBase _ (by omega) (by omega)]
                  have hstatusEq : decStatus bs off len d =
                      itemsStatus bs (pStartOf inBase rfH)
                        (pEndOf inBase rfH - pStartOf inBase rfH) (d - 1) := by
                    unfold decStatus itemsStatus
                    rw [hps, hpe]
                    have hdec := EvmAsm.EL.RLP.Ref.decodeD_long_list_items
                      (d - 1) hoff hgeF8 htr hb1ne
                      (by simpa [beVal_eq_winBE] using hbigVal)
                      (by simpa [beVal_eq_winBE] using hfitVal)
                    rw [show d = d - 1 + 1 by omega,
                      hdec]
                    have hlenPayload : off + len -
                        (off + 1 + ((bs.getD off 0).toNat - 0xF7)) =
                        beVal bs (off + 1) ((bs.getD off 0).toNat - 0xF7) := by
                      rw [hfitVal]
                      omega
                    rw [hlenPayload]
                    have hdminus : d - 1 + 1 - 1 = d - 1 := by omega
                    rw [hdminus]
                    cases hq : EvmAsm.EL.RLP.Ref.decodeJoinedEncodingsD (d - 1)
                        (EvmAsm.EL.RLP.Ref.win bs (off + 1 +
                          ((bs.getD off 0).toNat - 0xF7))
                          (EvmAsm.EL.RLP.Ref.winBE bs (off + 1)
                            ((bs.getD off 0).toNat - 0xF7))) with
                    | none =>
                      have hq' : EvmAsm.EL.RLP.Ref.decodeJoinedEncodingsD (d - 1)
                          (EvmAsm.EL.RLP.Ref.win bs (off + 1 +
                            ((bs.getD off 0).toNat - 0xF7))
                            (beVal bs (off + 1)
                              ((bs.getD off 0).toNat - 0xF7))) = none := by
                        simpa [beVal_eq_winBE] using hq
                      rw [hq']
                      simp
                    | some items =>
                      have hq' : EvmAsm.EL.RLP.Ref.decodeJoinedEncodingsD (d - 1)
                          (EvmAsm.EL.RLP.Ref.win bs (off + 1 +
                            ((bs.getD off 0).toNat - 0xF7))
                            (beVal bs (off + 1)
                              ((bs.getD off 0).toNat - 0xF7))) = some items := by
                        simpa [beVal_eq_winBE] using hq
                      rw [hq']
                      simp
                  have hrfR14 : rfR.get .x14 = rfL.get .x10 := by
                    rw [hrfL]
                    simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq,
                      reduceCtorEq, not_false_eq_true]
                  have hrfR13 : rfR.get .x13 = fp := by
                    rw [hrfL]
                    simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    rw [hfp, se12_n8]
                    simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
                      not_false_eq_true]
                    bv_omega
                  have hwsR' : wsR = wsL := by rw [hwsL]
                  have hstk : wsR.take 8 = dwordBytes v := by
                    rw [hwsR', hslot]
                    rw [hwsH.2, hwsR, hwsF, hwsP, hwsPeq, hwsB1, hwsQ2,
                      hwsSB, hwsCB, hwsB0, h2]
                    have hws0 : ws₀.length = 40 * d + 8 := by
                      have hh := hlenB0
                      rw [h2, length_setBytes] at hh
                      exact hh
                    have hs := setBytes_slot ws₀ (dwordBytes v) 0
                      (by
                        rw [length_dwordBytes, hws0]
                        omega)
                    rw [List.drop_zero, length_dwordBytes] at hs
                    exact hs
                  refine ⟨?_, hrfR13, hstk, hAc.trans (hAP.trans h3)⟩
                  rw [hrfR14, hstat, hstatusEq]
                · obtain ⟨rfF, wsF, hlenF, hrestF, hrfX, hwsX⟩ := TRbad
                  have hx14B1 : rfB.get .x14 = (1 : Word) := by
                    rw [hrfX]
                    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                      RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
                  have hx14B0 : rfB.get .x14 = (0 : Word) := hrfH
                  rw [hx14B1] at hx14B0
                  simp at hx14B0
          · have hx14B1 : rfB.get .x14 = (1 : Word) := by
              rw [hrfW]
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
            have hx14B0 : rfB.get .x14 = (0 : Word) := hrfH
            rw [hx14B1] at hx14B0
            simp at hx14B0
    · rcases hnogo with ⟨rfL, wsL, hlenL, hpreL, hrfL, hwsL⟩
      rcases hpreL with ⟨hcase, hnot⟩
      rcases hcase with hbudget | hshort | hlong
      · obtain ⟨rfX, wsX, hlenX, ⟨⟨R0, hnotbltu⟩, hbud⟩, hrfL1, hwsL1⟩ := hbudget
        obtain ⟨rf₁, ws₁, hlen₁, ⟨hExact, hne₁⟩, hrfX, hwsX⟩ := R0
        have hx11₁ : rf₁.get .x11 = BitVec.ofNat 64 len := by
          rw [hExact.1]
          exact hx11
        have hlen0 : 0 < len := by
          rcases Nat.eq_zero_or_pos len with hzero | hpos
          · apply False.elim
            apply hne₁
            change rf₁.get .x11 = rf₁.get .x0
            rw [hx11₁, hzero]
            simp
          · exact hpos
        have hoffb : off < bs.length := by omega
        have hset : (setBytes ws₀ 0 (dwordBytes v)).length = 40 * d + 8 := by
          rw [← hExact.2.1]
          exact hlen₁
        rw [hExact.1, hExact.2.1,
          b0_engine bs inBase fp _ L rf₀ (setBytes ws₀ 0 (dwordBytes v))
            hset off hx10 hoffb] at hrfX hwsX
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hrfL1 hwsL1 hrfX hwsX hrfL hwsL
        have hrfR' : rfR = rfL := by simpa using hrfL
        have hwsR' : wsR = wsL := by simpa using hwsL
        have hA : A = A₀ := hExact.2.2
        have hx14L : rfL.get .x14 = (1 : Word) := by
          rw [hrfL1]
          simp only [RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
        have hx13L : rfL.get .x13 = fp := by
          rw [hrfL1]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
          rw [hrfX]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
          exact hx13
        have hx12X : rfX.get .x12 = BitVec.ofNat 64 d := by
          rw [hrfX]
          simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq, not_false_eq_true]
          exact hx12
        have hd0 : d = 0 := by
          have hz : rfX.get .x12 = rfX.get .x0 := hbud
          rw [hx12X] at hz
          have hz' := congrArg BitVec.toNat hz
          simp only [BitVec.toNat_ofNat, RegFile.get_x0] at hz'
          rw [Nat.mod_eq_of_lt hd64] at hz'
          exact hz'
        have hws0 : ws₀.length = 40 * d + 8 := by
          have hh := hlen₁
          rw [hExact.2.1, length_setBytes] at hh
          exact hh
        have htk : (wsL).take 8 = dwordBytes v := by
          rw [hwsL1, hwsX]
          have hs := setBytes_slot ws₀ (dwordBytes v) 0
            (by rw [length_dwordBytes, hws0]; omega)
          rw [List.drop_zero, length_dwordBytes] at hs
          exact hs
        have hx5X : rfX.get .x5 = (bs.getD off 0).zeroExtend 64 := by
          rw [hrfX]
          simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
            reduceCtorEq, not_false_eq_true]
        have hx6X : rfX.get .x6 = (192 : Word) := by
          rw [hrfX]
          simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
            not_false_eq_true]
        have hgeC0 : 0xC0 ≤ (bs.getD off 0).toNat := by
          have h : ¬ (BitVec.ult (rfX.get .x5) (rfX.get .x6) = true) :=
            hnotbltu
          rw [hx5X, hx6X, ult_iff, toNat_zx] at h
          have hc : ((192 : Word)).toNat = 0xC0 := rfl
          omega
        refine ⟨?_, ?_, ?_, hA⟩
        · rw [hrfR', hx14L]
          simp [decStatus, hd0]
          exact EvmAsm.EL.RLP.Ref.decodeD_list_budget hoff hlen0 hgeC0
        · rw [hrfR', hx13L]
        · rw [hwsR']
          exact htk
      · simp only [listShortHdr, Stmt.sp] at hshort
        rcases hshort with ⟨rsl, ssl, hsl, hrest⟩
        rcases hrest with ⟨hleft, hrfLshort, hwsLshort⟩
        rcases hleft with ⟨hpre, hfitCond⟩
        have hx14L0 : rfL.get .x14 = (0 : Word) := by
          rw [hrfLshort]
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
            RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
        apply False.elim
        apply hnot
        change rfL.get .x14 = rfL.get .x0
        rw [hx14L0]
        simp
        all_goals
          rename_i hfail
          rcases hfail with ⟨rf1, ws1, hlen1, hrest1⟩
          rcases hrest1 with ⟨hpre1, hfinal⟩
          rcases hfinal with ⟨hrfLfail, hwsLfail⟩
          rcases hpre1 with ⟨hpreM, hfitNeg⟩
          rcases hpreM with ⟨rfM, wsM, hlenM, hrestM⟩
          rcases hrestM with ⟨hleftM, hbltM, hrfM, hwsM⟩
          rcases hleftM with ⟨hpreM0, hbltuM⟩
          rcases hpreM0 with ⟨rf0, ws0, hlen0, hrest0⟩
          rcases hrest0 with ⟨hleft0, hnotx12, hrfM0, hwsM0⟩
          rcases hleft0 with ⟨hpre0, hnotbltu0⟩
          rcases hpre0 with ⟨hpre00, hnotbltu00⟩
          rcases hpre00 with ⟨rfP, wsP, hlenP, hrestP⟩
          rcases hrestP with ⟨hreachP, hrf0, hws0⟩
          rcases hreachP with ⟨hExact, hneP⟩
          have hlenPos : 0 < len := by
            rcases Nat.eq_zero_or_pos len with hzero | hpos
            · apply False.elim
              apply hneP
              change rfP.get .x11 = rfP.get .x0
              rw [hExact.1, hx11, hzero]
              simp
            · exact hpos
          have hoffb : off < bs.length := by omega
          have hset : (setBytes ws₀ 0 (dwordBytes v)).length = 40 * d + 8 := by
            rw [← hExact.2.1]
            exact hlenP
          rw [hExact.1, hExact.2.1,
            b0_engine bs inBase fp _ L rf₀ (setBytes ws₀ 0 (dwordBytes v))
              hset off hx10 hoffb] at hrf0 hws0
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
            RegFile.get_set_self, ne_eq, reduceCtorEq,
            not_false_eq_true] at hrf0 hws0 hnotx12 hbltM hbltuM hrfLfail hwsLfail
          have hgeC0 : 0xC0 ≤ (bs.getD off 0).toNat := by
            have h : ¬ (BitVec.ult (rf0.get .x5) (rf0.get .x6) = true) :=
              hnotbltu00
            rw [hrf0] at h
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true] at h
            rw [ult_iff, toNat_zx] at h
            have hc : ((192 : Word)).toNat = 0xC0 := rfl
            omega
          have hleF7 : (bs.getD off 0).toNat ≤ 0xF7 := by
            have h : BitVec.ult (rfM.get .x5) (rfM.get .x6) = true := hbltuM
            rw [hnotx12, hrf0] at h
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true] at h
            rw [ult_iff, toNat_zx] at h
            have hc : ((248 : Word)).toNat = 0xF8 := rfl
            omega
          have hdpos : 1 ≤ d := by
            rcases Nat.eq_zero_or_pos d with hzero | hpos
            · apply False.elim
              apply hnotbltu0
              change rf0.get .x12 = rf0.get .x0
              rw [hrf0]
              simp only [RegFile.get_set_ne, ne_eq,
                reduceCtorEq, not_false_eq_true]
              rw [hx12, hzero]
              simp
            · exact hpos
          have hx7R1 : rf1.get .x7 = BitVec.ofNat 64
              ((bs.getD off 0).toNat - 0xC0) := by
            rw [hbltM]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hnotx12]
            simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hrf0]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [se12_nC0]
            bv_omega
          have hx6R1 : rf1.get .x6 = BitVec.ofNat 64
              ((bs.getD off 0).toNat - 0xC0) + 1 := by
            rw [hbltM]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hnotx12]
            simp only [RegFile.get_set_ne, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [hrf0]
            simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
              reduceCtorEq, not_false_eq_true]
            rw [se12_nC0, se12_1]
            bv_omega
          have hx11R1 : rf1.get .x11 = BitVec.ofNat 64 len := by
            rw [hbltM]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hnotx12]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrf0]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hx11
          have hfitBad : len ≠ 1 + ((bs.getD off 0).toNat - 0xC0) := by
            intro hfit
            apply hfitNeg
            change rf1.get .x6 = rf1.get .x11
            rw [hx6R1, hx11R1]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat]
            have h1n : ((1 : Word)).toNat = 1 := rfl
            omega
          have hrfR' : rfR = rfL := by simpa using hrfL
          have hwsR' : wsR = wsL := by simpa using hwsL
          have hx14L : rfL.get .x14 = (1 : Word) := by
            rw [hrfLfail]
            simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
              not_false_eq_true]
          have hx13L : rfL.get .x13 = fp := by
            rw [hrfLfail]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hbltM]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hnotx12]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            rw [hrf0]
            simp only [RegFile.get_set_ne, ne_eq, reduceCtorEq,
              not_false_eq_true]
            exact hx13
          have hws0len : ws₀.length = 40 * d + 8 := by
            have hh := hlen0
            rw [hws0, length_setBytes] at hh
            exact hh
          have htk : wsL.take 8 = dwordBytes v := by
            rw [hwsLfail, hws0]
            have hs := setBytes_slot ws₀ (dwordBytes v) 0
              (by rw [length_dwordBytes, hws0len]; omega)
            rw [List.drop_zero, length_dwordBytes] at hs
            exact hs
          refine ⟨?_, ?_, ?_, hExact.2.2⟩
          · rw [hrfR', hx14L]
            have hdl := EvmAsm.EL.RLP.Ref.decodeD_short_list_badlen (d - 1)
              hoff hlenPos hgeC0 hleF7 hfitBad
            have hdl' : EvmAsm.EL.RLP.Ref.decodeD d
                (EvmAsm.EL.RLP.Ref.win bs off len) = none := by
              rw [show d = (d - 1) + 1 by omega]
              exact hdl
            rw [decStatus_none hdl']
          · rw [hrfR', hx13L]
          · rw [hwsR']
            exact htk
      · have hlong' : Stmt.sp ⟨inBase, bs⟩ (⟨fp, 40 * d + 8⟩ : RwRegion)
            (listLongHdr beS) (longHdrReach bs inBase fp d v rf₀ ws₀ A₀)
            rfL wsL A := by
          unfold longHdrReach
          exact hlong
        exact post_core_nogo_long bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS
          rfR wsR A rfL wsL L hoff hx10 hx11 hx12 hx13 hbePost hitPost hnot
          hrfL hwsL hlong'


-- ============================================================================
-- The decoder body specification
-- ============================================================================

private theorem decPin_flat :
    decFnPin.body.offsetsOk = true ∧ 4 * decFnPin.body.size < 2 ^ 64 := by
  constructor
  · decide +kernel
  · decide +kernel

private theorem dec_offsetsOk_eq (beS itemsS : FnHandleS) :
    (decBody beS itemsS).offsetsOk = decFnPin.body.offsetsOk := rfl

private theorem dec_size_eq (beS itemsS : FnHandleS) :
    (decBody beS itemsS).size = decFnPin.body.size := rfl

/-- The decoder body specification, per exact entry state. -/
theorem decFnV_spec (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (off len : Nat) (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (beS itemsS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (hoff : off + len ≤ bs.length)
    (hx10 : rf₀.get .x10 = inBase + BitVec.ofNat 64 off)
    (hx11 : rf₀.get .x11 = BitVec.ofNat 64 len)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
    (hd64 : d < 2 ^ 64)
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
          ∧ A = A₁) :
    (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS).SpecR
      (decEntry + 4) decCr := by
  show Fn.SpecR _ _ _
  vcgenK
  case region => exact ⟨L.regWf, L.rwWf⟩
  case rlpdec.flat =>
    refine ⟨?_, ?_⟩
    · rw [show (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS
          itemsS).body.offsetsOk = decFnPin.body.offsetsOk from
        dec_offsetsOk_eq beS itemsS]
      exact decPin_flat.1
    · rw [show (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS
          itemsS).body.size = decFnPin.body.size from
        dec_size_eq beS itemsS]
      exact decPin_flat.2
  case code =>
    intro a i h
    have h' : CodeReq.ofProg (decEntry + 4)
        (decFnPin.body.flatten (decEntry + 4)) a = some i := by
      rw [show (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS
          itemsS).body.flatten (decEntry + 4)
        = decFnPin.body.flatten (decEntry + 4) from
          decBody_flatten beS itemsS hbeE hitE] at h
      exact h
    have h2 : CodeReq.ofProg decEntry decProg a = some i := by
      show CodeReq.ofProg decEntry (.SD .x13 .x1 0 ::
          (decFnPin.body.flatten (decEntry + 4)
            ++ [.LD .x1 .x13 0, .JALR .x0 .x1 0])) a = some i
      refine ofProg_cons_tail ?_ a i (ofProg_mono_left a i h')
      rw [List.length_append, decBodyFlat_len]
      decide
    simp only [decCr, CodeReq.union, h2]
  case callees =>
    exact decBody_calleesIn bs inBase d fp beS itemsS hbeCode hbeReg hbeRw
      hitCode hitReg hitRw
  case calls => exact hcalls
  case rlpdec.post =>
    intro rf ws A hsp
    exact post_core bs inBase d fp off len v rf₀ ws₀ A₀ beS itemsS rf ws A
      L hoff hx10 hx11 hx12 hx13 hd64 hbePost hitPost hsp
  case rlpdec.empty.e.b0.mem =>
    rintro rf ws A hws ⟨⟨h1, -, -⟩, hne⟩
    have hb : inBase.toNat + bs.length < 2 ^ 64 := L.regWf.2.1
    rw [h1] at hne
    have hlen0 : 0 < len := by
      rcases Nat.eq_zero_or_pos len with h0 | hp
      · exact absurd (by rw [hx11, h0]; simp :
          rf₀.get .x11 = rf₀.get .x0) hne
      · exact hp
    have hoffb : off < bs.length := by omega
    have haddr : rf.get .x10 + signExtend12 (0 : BitVec 12)
        = inBase + BitVec.ofNat 64 off := by
      rw [se12_0, h1, hx10]
      bv_omega
    have hnorw : ¬ inRw fp ws (rf.get .x10 + signExtend12 (0 : BitVec 12))
        1 := by
      rw [haddr]
      exact L.not_inRw hws hoffb
    simp only [decFnV, decRw, blockVCs, loadSem, storeSem]
    refine ⟨?_, trivial, trivial⟩
    -- `simp` normalised the routing condition but left the `Decidable`
    -- argument of the `ite` spelled through `decFnV`/`decRw`, so
    -- `rw [if_neg …]` can no longer assign it.  Restating the goal with the
    -- canonical instance (`show` checks at default transparency) repairs it.
    show (if inRw fp ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 then
            (Region.mk fp ws).loadOk
              (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1
          else
            (Region.mk inBase bs).loadOk
              (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1)
    rw [if_neg hnorw, haddr]
    exact region_loadOk1 L.regWf hoffb
  case rlpdec.empty.e.disp.t.single.e.shortb.t.sbfit.t.sbcanon.t.sbb1.mem =>
    rintro rf ws A hws ⟨⟨rfS1, wsS1, -, ⟨hR4, hsbfit⟩, hrf5, -⟩, hsbcanon⟩
    obtain ⟨rfSB, wsSB, -, ⟨hR3, -⟩, hrf4, -⟩ := hR4
    obtain ⟨rfB8, wsB8, -, ⟨hR2, hnsingle⟩, hrf3, -⟩ := hR3
    obtain ⟨rfC8, wsC8, -, ⟨hR1, -⟩, hrf2, -⟩ := hR2
    obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hR1
    exact sbb1_mem_core bs inBase d fp off len rf₀ rfB0 rfC8 rfB8 rfSB rfS1
      rf wsB0 wsC8 wsB8 wsSB wsS1 ws L hoff hx10 hx11 hws hlB0 h1 hne hrf1
      hrf2 hnsingle hrf3 hrf4 hsbfit hrf5 hsbcanon
  case rlpdec.empty.e.disp.t.single.e.shortb.e.lbtr.t.lbb1.mem =>
    rintro rf ws A hws ⟨⟨rfLB, wsLB, -, ⟨hR3, hnshortb⟩, hrf4, -⟩, hlbtr⟩
    obtain ⟨rfB8, wsB8, -, ⟨hR2, -⟩, hrf3, -⟩ := hR3
    obtain ⟨rfC8, wsC8, -, ⟨hR1, -⟩, hrf2, -⟩ := hR2
    obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hR1
    exact lbb1_mem_core bs inBase d fp off len rf₀ rfB0 rfC8 rfB8 rfLB rf
      wsB0 wsC8 wsB8 wsLB ws L hoff hx10 hx11 hws hlB0 h1 hne hrf1 hrf2
      hrf3 hrf4 hnshortb hlbtr
  case rlpdec.empty.e.disp.t.single.e.shortb.e.lbtr.t.lbz.e.lbbe.pre =>
    rintro rf ws A ⟨rfB1, wsB1, -, ⟨hR5, -⟩, hrf6, -⟩
    obtain ⟨rfLB2, wsLB2, -, ⟨hR4, hlbtr⟩, hrf5, -⟩ := hR5
    obtain ⟨rfLB, wsLB, -, ⟨hR3, hnshortb⟩, hrf4, -⟩ := hR4
    obtain ⟨rfB8, wsB8, -, ⟨hR2, -⟩, hrf3, -⟩ := hR3
    obtain ⟨rfC8, wsC8, -, ⟨hR1, hdisp⟩, hrf2, -⟩ := hR2
    obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hR1
    exact lbbe_pre_core bs inBase d fp off len rf₀ rfB0 rfC8 rfB8 rfLB
      rfLB2 rfB1 rf wsB0 wsC8 wsB8 wsLB wsLB2 wsB1 ws beS L hoff hx10 hx11
      hbeE hbePre A hlB0 h1 hne hrf1 hdisp hrf2 hrf3 hnshortb hrf4 hlbtr
      hrf5 hrf6
  case rlpdec.empty.e.disp.e.bud.e.listd.e.lltr.t.llb1.mem =>
    rintro rf ws A hws ⟨⟨rfLL, wsLL, -, ⟨hR2, hnlistd⟩, hrf3, -⟩, hlltr⟩
    obtain ⟨rfBD, wsBD, -, ⟨⟨hR1, -⟩, -⟩, hrf2, -⟩ := hR2
    obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hR1
    exact llb1_mem_core bs inBase d fp off len rf₀ rfB0 rfBD rfLL rf wsB0
      wsBD wsLL ws L hoff hx10 hx11 hws hlB0 h1 hne hrf1 hrf2 hrf3 hnlistd
      hlltr
  case rlpdec.empty.e.disp.e.bud.e.listd.e.lltr.t.llz.e.llbe.pre =>
    rintro rf ws A ⟨rfB1, wsB1, -, ⟨hR4, -⟩, hrf5, -⟩
    obtain ⟨rfLL2, wsLL2, -, ⟨hR3, hlltr⟩, hrf4, -⟩ := hR4
    obtain ⟨rfLL, wsLL, -, ⟨hR2, hnlistd⟩, hrf3, -⟩ := hR3
    obtain ⟨rfBD, wsBD, -, ⟨⟨hR1, -⟩, -⟩, hrf2, -⟩ := hR2
    obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hR1
    exact llbe_pre_core bs inBase d fp off len rf₀ rfB0 rfBD rfLL rfLL2
      rfB1 rf wsB0 wsBD wsLL wsLL2 wsB1 ws beS L hoff hx10 hx11 hbeE hbePre
      A hlB0 h1 hne hrf1 hrf2 hnlistd hrf3 hlltr hrf4 hrf5
  case rlpdec.empty.e.disp.e.lgo.t.items.pre =>
    rintro rf ws A ⟨rfG, wsG, -, ⟨hDisp, hlgo⟩, hrf9, -⟩
    change rfG.get .x14 = rfG.get .x0 at hlgo
    rcases hDisp with hDeep | hElse
    · -- st_deep poisons: killed by the lgo condition
      obtain ⟨rfX, wsX, -, -, hrfGx, -⟩ := hDeep
      exfalso
      have h14 : rfG.get .x14 = (1 : Word) := by
        rw [hrfGx]
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
          RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
      rw [h14, RegFile.get_x0] at hlgo
      exact absurd hlgo (by decide)
    · rcases hElse with hShort | hLong
      · -- short-list header
        rcases hShort with hSLGO | hBadSL
        · obtain ⟨rfF', wsF', -, ⟨hSl, hslfit⟩, hrfG, hwsG⟩ := hSLGO
          obtain ⟨rfSL, wsSL, -, ⟨hBudm, -⟩, hrf3, -⟩ := hSl
          obtain ⟨rfBD, wsBD, -, ⟨⟨hB0, hndisp⟩, hnbud⟩, hrf2, -⟩ := hBudm
          obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hB0
          have hws2 : wsG = wsF' := by
            rw [hwsG]
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          exact items_pre_short_core bs inBase d fp off len rf₀ rfB0 rfBD
            rfSL rfF' rf wsB0 wsBD wsSL wsF' ws itemsS L hoff hx10 hx11
            hx12 hx13 hd64 hitE hitPre A hlB0 h1 hne hrf1 hndisp hnbud hrf2
            hrf3 hslfit (by rw [hrf9, hrfG, hws2]; rfl)
        · obtain ⟨rfX, wsX, -, -, hrfGx, -⟩ := hBadSL
          exfalso
          have h14 : rfG.get .x14 = (1 : Word) := by
            rw [hrfGx]
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
              RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
          rw [h14, RegFile.get_x0] at hlgo
          exact absurd hlgo (by decide)
      · -- long-list header
        rcases hLong with hThen | hLLTR
        · rcases hThen with hLLZ | hRest
          · obtain ⟨rfX, wsX, -, -, hrfGx, -⟩ := hLLZ
            exfalso
            have h14 : rfG.get .x14 = (1 : Word) := by
              rw [hrfGx]
              simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
                RegFile.get_set_self, ne_eq, reduceCtorEq,
                not_false_eq_true]
            rw [h14, RegFile.get_x0] at hlgo
            exact absurd hlgo (by decide)
          · rcases hRest with hSM | hGO_BAD
            · obtain ⟨rfX, wsX, -, -, hrfGx, -⟩ := hSM
              exfalso
              have h14 : rfG.get .x14 = (1 : Word) := by
                rw [hrfGx]
                simp only [execBlock_cons, execBlock_nil, execInstrRF,
                  aluSem, RegFile.get_set_self, ne_eq, reduceCtorEq,
                  not_false_eq_true]
              rw [h14, RegFile.get_x0] at hlgo
              exact absurd hlgo (by decide)
            · rcases hGO_BAD with hGO | hBAD
              · -- the live GO arm: recursive items call
                obtain ⟨rfF, wsF, -, ⟨hFit, hllfit2⟩, hrf8, hwsG8⟩ := hGO
                obtain ⟨rfC38, wsC38, -, ⟨hCall, hnsmall⟩, hrf7, -⟩ := hFit
                obtain ⟨rfP, wsP, -, hCall2, hrf6, -⟩ := hCall
                obtain ⟨rf₁, ws₁, A₁, hPre, hpre, hpost⟩ := hCall2
                obtain ⟨rfB1, wsB1, -, ⟨hLlb1, -⟩, hrf5, -⟩ := hPre
                obtain ⟨rfLL2, wsLL2, -, ⟨hLl, hlltr⟩, hrf4, -⟩ := hLlb1
                obtain ⟨rfLL, wsLL, -, ⟨hBudm, hnlistd⟩, hrf3, -⟩ := hLl
                obtain ⟨rfBD, wsBD, -, ⟨⟨hB0, -⟩, hnbud⟩, hrf2, -⟩ := hBudm
                obtain ⟨rfB0, wsB0, hlB0, ⟨⟨h1, -, -⟩, hne⟩, hrf1, -⟩ := hB0
                exact items_pre_long_core bs inBase d fp off len rf₀ rfB0
                  rfBD rfLL rfLL2 rfB1 rf₁ rfP rfC38 rfF rfG rf wsB0 wsBD
                  wsLL wsLL2 wsB1 ws₁ wsP wsC38 wsF wsG ws A₁ A beS itemsS
                  L hoff hx10 hx11 hx12 hx13 hd64 hitE hitPre hbePost A
                  hlB0 h1 hne hrf1 hnbud hrf2 hnlistd hrf3 hlltr hrf4 hrf5
                  hpost hrf6 hnsmall hrf7 hllfit2 hrf8 hrf9
              · obtain ⟨rfX, wsX, -, -, hrfGx, -⟩ := hBAD
                exfalso
                have h14 : rfG.get .x14 = (1 : Word) := by
                  rw [hrfGx]
                  simp only [execBlock_cons, execBlock_nil, execInstrRF,
                    aluSem, RegFile.get_set_self, ne_eq, reduceCtorEq,
                    not_false_eq_true]
                rw [h14, RegFile.get_x0] at hlgo
                exact absurd hlgo (by decide)
        · obtain ⟨rfX, wsX, -, -, hrfGx, -⟩ := hLLTR
          exfalso
          have h14 : rfG.get .x14 = (1 : Word) := by
            rw [hrfGx]
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
              RegFile.get_set_self, ne_eq, reduceCtorEq, not_false_eq_true]
          rw [h14, RegFile.get_x0] at hlgo
          exact absurd hlgo (by decide)
  all_goals try decide


end RecDecode
end SAsm
end EvmAsm.Rv64
