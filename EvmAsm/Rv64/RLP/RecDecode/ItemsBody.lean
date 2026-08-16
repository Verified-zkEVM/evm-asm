/-
  EvmAsm.Rv64.RLP.RecDecode.ItemsBody

  The body specification of `rlp_items` (`decode_joined_encodings`): the
  sibling cursor loop.  The invariant `decInv` carries the loop's meaning —
  the remaining suffix decides the whole payload — and the per-iteration
  step is the machine transcription of the reference's loop body:
  `decode_item_length` (the header cascade), the caller-side fit check,
  the recursive `decode` on the exact item window, the cursor advance.
-/

import EvmAsm.Rv64.RLP.RecDecode.Body
import EvmAsm.Rv64.RLP.RecDecode.VcgenK

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)
open EvmAsm.EL.RLP.Ref (decodeD decodeJoinedEncodingsD decodeItemLength win
  winBE)

/-- The items body specification, per exact entry state. -/
theorem itemsFnV_spec (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (beS childS : FnHandleS)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (hpq : pStart ≤ pEnd)
    (hq : pEnd ≤ bs.length)
    (hx15 : rf₀.get .x15 = inBase + BitVec.ofNat 64 pStart)
    (hx16 : rf₀.get .x16 = inBase + BitVec.ofNat 64 pEnd)
    (hx12 : rf₀.get .x12 = BitVec.ofNat 64 d)
    (hx13 : rf₀.get .x13 = fp)
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
    (itemsFnV bs inBase d fp pStart pEnd v rf₀ ws₀ A₀ beS childS).SpecR
      (itemsEntry + 4) decCr := by
  show Fn.SpecR _ _ _
  vcgenK
  run_tac do
    for g in ← Lean.Elab.Tactic.getUnsolvedGoals do
      Lean.logInfo m!"CASE {← g.getTag}"
  all_goals sorry

end RecDecode
end SAsm
end EvmAsm.Rv64
