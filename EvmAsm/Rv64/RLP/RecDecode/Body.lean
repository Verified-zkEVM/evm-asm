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
import EvmAsm.Rv64.BitAux

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)
open EvmAsm.EL.RLP.Ref (decodeD decodeJoinedEncodingsD decodeItemLength win)

/-- The ghost-indexed body post: status for the entry window, frame
    pointer and `ra` slot intact, ambient untouched. -/
def decPostV (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
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
def itemsPostV (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
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

/-- The flattened decoder body is handle-independent (kernel-checked once,
    in its own declaration so the elaboration cost is paid once). -/
private theorem decBody_flatten (beS itemsS : FnHandleS) :
    (decBody beS itemsS).flatten (decEntry + 4)
      = decFnPin.body.flatten (decEntry + 4) := rfl

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
  all_goals first
    | trivial
    | (intro h hmem
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
       subst hmem
       first
         | exact ⟨hbeCode, hbeReg, hbeRw⟩
         | exact ⟨hitCode, hitReg, hitRw⟩)

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

set_option maxRecDepth 8000 in
private theorem decBody_callsOk (beS itemsS : FnHandleS)
    (hbeE : beS.entry = rdbeEntry) (hitE : itemsS.entry = itemsEntry) :
    (decBody beS itemsS).callsOk (decEntry + 4) := by
  and_intros
  all_goals first
    | (apply and_not_one_of_even
       have h1 : decEntry.toNat = 0x1000 := rfl
       have h4 : ((4 : Word)).toNat = 4 := rfl
       simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1, h4]
       omega)
    | (intro h hmem
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
       subst hmem
       first
         | (rw [hbeE]; decide)
         | (rw [hitE]; decide))
    | trivial

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
  vcgen
  case region => exact ⟨L.regWf, L.rwWf⟩
  case code =>
    intro a i h
    have h' : CodeReq.ofProg (decEntry + 4)
        (decFnPin.body.flatten (decEntry + 4)) a = some i := by
      rw [show (decFnV bs inBase d fp off len v rf₀ ws₀ A₀ beS
          itemsS).body.flatten (decEntry + 4)
        = decFnPin.body.flatten (decEntry + 4) from
          decBody_flatten beS itemsS] at h
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
  case calls =>
    exact decBody_callsOk beS itemsS hbeE hitE
  all_goals sorry

end RecDecode
end SAsm
end EvmAsm.Rv64
