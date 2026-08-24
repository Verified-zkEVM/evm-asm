/-
  EvmAsm.Rv64.RLP.RecDecode.Contract

  The contract tower for the recursive decoder pair:

  * `decPreS` / `decPostS` — the snapshot calling contract of `rlp_decode`
    at budget `d`, frame `fp`: the entry registers name a window
    `(off, len)`; the exit `x10` is `decStatus bs off len d`, `x13`
    restored, ambient untouched.
  * `itemsPreS` / `itemsPostS` — the same for `rlp_items`
    (`decode_joined_encodings`): the entry `x15`/`x16` name a payload
    window; the exit `x10` is `itemsStatus` at the same budget.
  * `DecSound` / `ItemsSound` — the soundness families (plain `Prop`s;
    the only recursive components, closed by the mutual ladder in
    `Knot.lean`: `DecSound (d+1)` from `ItemsSound d`, `ItemsSound d`
    from `DecSound d`).
  * `decInv` — the sibling-loop invariant (the machine transcription of
    `decode_joined_encodings`' induction).

  Frames: `rlp_decode` owns `⟨fp, 40·d + 8⟩` (its `ra` dword, then
  `rlp_items`' window); `rlp_items` owns `⟨fp, 40·d + 40⟩` (its
  `[ra][next-cursor][end][budget]` frame, then the child decoder's
  window).  The budget strictly decreases at the single recursive cycle
  `decode(d+1) → items(d) → decode(d)`.
-/

import EvmAsm.Rv64.RLP.RecDecode.DecodeFn

namespace EvmAsm.Rv64
namespace SAsm
namespace RecDecode

open Stmt
open EvmAsm.EL.RLP (Byte)
open EvmAsm.EL.RLP.Ref (decodeD decodeJoinedEncodingsD decodeItemLength win)

/-- `rlp_decode`'s writable region at budget `d`. -/
def decRw (d : Nat) (fp : Word) : RwRegion := ⟨fp, 40 * d + 8⟩

/-- `rlp_items`' writable region at budget `d`. -/
def itemsRw (d : Nat) (fp : Word) : RwRegion := ⟨fp, 40 * d + 40⟩

/-- Window named by the argument registers of a decoder entry state. -/
def offOf (inBase : Word) (rf : RegFile) : Nat := idxOf inBase (rf.get .x10)
def lenOf (rf : RegFile) : Nat := (rf.get .x11).toNat

/-- Payload window named by the registers of an items entry state. -/
def pStartOf (inBase : Word) (rf : RegFile) : Nat := idxOf inBase (rf.get .x15)
def pEndOf (inBase : Word) (rf : RegFile) : Nat := idxOf inBase (rf.get .x16)

/-- Caller-facing precondition of `rlp_decode` at `(d, fp)`. -/
def decPreS (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word) : Reach :=
  fun rf _ _ => ∃ off len : Nat,
    rf.get .x10 = inBase + BitVec.ofNat 64 off ∧
    rf.get .x11 = BitVec.ofNat 64 len ∧
    rf.get .x12 = BitVec.ofNat 64 d ∧
    rf.get .x13 = fp ∧
    off + len ≤ bs.length

/-- Snapshot postcondition of `rlp_decode`: status keyed to the entry
    window; frame pointer restored; ambient untouched.  The window content
    is unconstrained (the routine scribbles its own frame; the caller's
    frame is outside this window, preserved by `FnHandleS.widenPrefix`). -/
def decPostS (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ _ A₀ rf _ A =>
    rf.get .x10 = decStatus bs (offOf inBase rf₀) (lenOf rf₀) d
    ∧ rf.get .x13 = fp
    ∧ A = A₀

/-- Caller-facing precondition of `rlp_items` at `(d, fp)`. -/
def itemsPreS (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word) :
    Reach :=
  fun rf _ _ => ∃ p q : Nat,
    rf.get .x15 = inBase + BitVec.ofNat 64 p ∧
    rf.get .x16 = inBase + BitVec.ofNat 64 q ∧
    rf.get .x12 = BitVec.ofNat 64 d ∧
    rf.get .x13 = fp ∧
    p ≤ q ∧ q ≤ bs.length

/-- Snapshot postcondition of `rlp_items`. -/
def itemsPostS (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ _ A₀ rf _ A =>
    rf.get .x10 = itemsStatus bs (pStartOf inBase rf₀)
        (pEndOf inBase rf₀ - pStartOf inBase rf₀) d
    ∧ rf.get .x13 = fp
    ∧ A = A₀

/-- A dead snapshot handle with chosen regions and step budget. -/
def deadHandleSN (reg : Region) (rw : RwRegion) (n : Nat) : FnHandleS where
  entry := decEntry
  code := CodeReq.empty
  nSteps := n
  region := reg
  rw := rw
  pre := fun _ _ _ => False
  post := fun _ _ _ _ _ _ => False
  sound := fun _ _ _ _ _ hpre => hpre.elim

/-- The leaf's packaged step budget. -/
def rdbeSteps : Nat := (readBeFn 0 [] 0 0).body.steps + 1

/-- Step budgets of the two packaged routines at budget `d` over inputs of
    length ≤ `N`, defined through the bodies' own static step counts so
    they are definitionally what `retSpecR` produces.  (`.1` = decoder,
    `.2` = items.) -/
def stepsPair (N : Nat) : Nat → Nat × Nat
  | 0 =>
    let ds := 3 + (decBody (deadHandleSN Region.empty RwRegion.empty rdbeSteps)
      (deadHandleSN Region.empty RwRegion.empty 0)).steps
    (ds, 3 + (itemsBody N (fun _ _ _ _ => True)
      (deadHandleSN Region.empty RwRegion.empty rdbeSteps)
      (deadHandleSN Region.empty RwRegion.empty ds)).steps)
  | d + 1 =>
    let ds := 3 + (decBody (deadHandleSN Region.empty RwRegion.empty rdbeSteps)
      (deadHandleSN Region.empty RwRegion.empty (stepsPair N d).2)).steps
    (ds, 3 + (itemsBody N (fun _ _ _ _ => True)
      (deadHandleSN Region.empty RwRegion.empty rdbeSteps)
      (deadHandleSN Region.empty RwRegion.empty ds)).steps)

def decSteps (N d : Nat) : Nat := (stepsPair N d).1
def itemsSteps (N d : Nat) : Nat := (stepsPair N d).2

/-- Soundness of `rlp_decode`'s handle contract at `(d, fp)`. -/
def DecSound (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word) : Prop :=
  RdLayout inBase bs fp (40 * d + 8) →
  ∀ rf₀ ws₀ A₀, ws₀.length = 40 * d + 8 → Assertion.pcFree A₀ →
    decPreS bs inBase d fp rf₀ ws₀ A₀ →
    ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin (decSteps bs.length d) decEntry ret decCr
        (((.x1 : Reg) ↦ᵣ ret)
          ** asrtM ⟨inBase, bs⟩ (decRw d fp) (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret)
          ** asrtM ⟨inBase, bs⟩ (decRw d fp) (decPostS bs inBase d fp rf₀ ws₀ A₀))

/-- Soundness of `rlp_items`' handle contract at `(d, fp)`. -/
def ItemsSound (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word) : Prop :=
  RdLayout inBase bs fp (40 * d + 40) →
  ∀ rf₀ ws₀ A₀, ws₀.length = 40 * d + 40 → Assertion.pcFree A₀ →
    itemsPreS bs inBase d fp rf₀ ws₀ A₀ →
    ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin (itemsSteps bs.length d) itemsEntry ret decCr
        (((.x1 : Reg) ↦ᵣ ret)
          ** asrtM ⟨inBase, bs⟩ (itemsRw d fp) (Reach.exact rf₀ ws₀ A₀))
        (((.x1 : Reg) ↦ᵣ ret)
          ** asrtM ⟨inBase, bs⟩ (itemsRw d fp)
              (itemsPostS bs inBase d fp rf₀ ws₀ A₀))

/-- `rlp_decode`'s handle contents at `(d, fp)`. -/
def decHandleSAt (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (L : RdLayout inBase bs fp (40 * d + 8))
    (snd : DecSound bs inBase d fp) : FnHandleS where
  entry := decEntry
  code := decCr
  nSteps := decSteps bs.length d
  region := ⟨inBase, bs⟩
  rw := decRw d fp
  pre := decPreS bs inBase d fp
  post := decPostS bs inBase d fp
  sound := snd L

/-- `rlp_items`' handle contents at `(d, fp)`. -/
def itemsHandleSAt (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (L : RdLayout inBase bs fp (40 * d + 40))
    (snd : ItemsSound bs inBase d fp) : FnHandleS where
  entry := itemsEntry
  code := decCr
  nSteps := itemsSteps bs.length d
  region := ⟨inBase, bs⟩
  rw := itemsRw d fp
  pre := itemsPreS bs inBase d fp
  post := itemsPostS bs inBase d fp
  sound := snd L

/-- The sibling-loop invariant at ghosts
    `(bs, inBase, d = the loop's budget, fp, pStart, pEnd, v, A₀)`;
    `c` is the cursor, `i` the iteration count.  The status flag either
    attests that the remaining suffix decides the whole payload, or that
    the payload is rejected and the cursor was forced to the end. -/
def decInv (bs : List Byte) (inBase : Word) (d : Nat) (fp : Word)
    (pStart pEnd : Nat) (v : Word) (A₀ : Assertion) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    ∃ c : Nat,
      pStart ≤ c ∧ c ≤ pEnd ∧ pStart + i ≤ c
      ∧ rf.get .x15 = inBase + BitVec.ofNat 64 c
      ∧ rf.get .x16 = inBase + BitVec.ofNat 64 pEnd
      ∧ rf.get .x12 = BitVec.ofNat 64 d
      ∧ rf.get .x13 = fp
      ∧ ws.take 8 = dwordBytes v
      ∧ ws.length = 40 * d + 40
      ∧ A = A₀
      ∧ ((rf.get .x14 = 0
          ∧ ((decodeJoinedEncodingsD d (win bs c (pEnd - c))).isSome
            ↔ (decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart))).isSome))
        ∨ (rf.get .x14 = 1
          ∧ decodeJoinedEncodingsD d (win bs pStart (pEnd - pStart)) = none
          ∧ c = pEnd))

end RecDecode
end SAsm
end EvmAsm.Rv64
