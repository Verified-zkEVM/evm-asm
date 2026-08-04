/-
  EvmAsm.Codegen.Programs.BytesToNibblesBridge

  GH #11344 — the reference tie for `bytes_to_nibbles`, row 1 of
  `docs/leaf-routine-targets.md`.

  WHAT ALREADY EXISTED. `bytesToNibblesFn_spec` (`BytesToNibblesSAsm.lean:272`) proves
  the structured SAsm contract: the destination region ends up holding
  `bytesToNibblesBytes srcBytes len`, with the counted loop's invariant already
  discharged by `vcgen`. The loop work is done; this module does not touch it.

  WHAT WAS MISSING. `bytesToNibblesBytes` (`:31`) is a *local* accumulator —
  `nibblePrefix`, built by repeated `++ nibblePair (srcBytes.getD i 0)` — and
  `nibblePair` is phrased with `BitVec.truncate`/`signExtend12` because that is how the
  emitted `SRLI`/`ANDI` behave. The reference `keyToNibbles`
  (`SpecRef/WitnessState.lean:78`) is a one-line `List.flatMap` over `>>> 4` and
  `&&& 0x0F`. Same function, but nothing said so.

  THREE STEPS, and the middle one is the only real content:
  * `highNibble_eq` / `lowNibble_eq` — the machine's truncate-and-shift IS the
    reference's arithmetic on the byte. Per-bit, no `bv_decide`.
  * `nibblePrefix_eq_keyToNibbles_take` — the accumulator equals the `flatMap`, by
    induction on the counter. `nibblePrefix` grows on the RIGHT (`prefix ++ pair i`)
    while `flatMap` grows on the LEFT, so the induction step needs
    `List.take_succ` to expose the last element rather than the first — that mismatch
    is the whole difficulty.
  * `bytesToNibblesBytes_eq_keyToNibbles` — the two composed, in the form the routine's
    post can be rewritten with.

  ⚠️ SCOPE. #11344 also names the nibble-expansion half of `compact_to_nibbles`
  (`SpecRef/IncrementalMpt.lean`) — that half only, not the flag decode. The bridge here
  is exactly that half: `keyToNibbles` is what `compact_to_nibbles` calls for the
  expansion, so no separate lemma is needed.
-/

import EvmAsm.Codegen.Programs.BytesToNibblesSAsm
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Stateless.SpecRef.WitnessState

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace BytesToNibblesSAsm

/-- Widening a byte to 64 bits leaves its value alone — the `% 2 ^ 64` that
    `toNat_setWidth` introduces is the identity here. -/
private theorem byte_mod (b : BitVec 8) : b.toNat % 2 ^ 64 = b.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by norm_num))

/-- The machine's `SRLI 4` on a widened byte is the reference's `>>> 4`. -/
theorem highNibble_eq (b : BitVec 8) :
    highNibble b = BitVec.ofNat 8 (b.toNat >>> 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [highNibble, BitVec.truncate, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, byte_mod, BitVec.toNat_ofNat]

/-- The machine's `ANDI 15` on a widened byte is the reference's `&&& 0x0F`. -/
theorem lowNibble_eq (b : BitVec 8) :
    lowNibble b = BitVec.ofNat 8 (b.toNat &&& 0x0F) := by
  apply BitVec.eq_of_toNat_eq
  have h15 : signExtend12 (15 : BitVec 12) = (15 : Word) := by decide
  simp only [lowNibble, h15, BitVec.truncate, BitVec.toNat_setWidth,
    BitVec.toNat_and, byte_mod, BitVec.toNat_ofNat,
    show ((15 : Word)).toNat = 15 from by decide]

/-- The routine's nibble pair is the reference's. -/
theorem nibblePair_eq (b : BitVec 8) :
    nibblePair b = [BitVec.ofNat 8 (b.toNat >>> 4), BitVec.ofNat 8 (b.toNat &&& 0x0F)] := by
  rw [nibblePair, highNibble_eq, lowNibble_eq]

/-- ⭐ **The accumulator IS the reference's `flatMap`.** Induction on the counter; the
    step exposes the LAST element of the window (`List.take_succ`) because
    `nibblePrefix` appends on the right while `flatMap` builds on the left. -/
theorem nibblePrefix_eq_keyToNibbles_take (srcBytes : List (BitVec 8)) (i : Nat)
    (hi : i ≤ srcBytes.length) :
    nibblePrefix srcBytes i
      = EvmAsm.Stateless.SpecRef.keyToNibbles (srcBytes.take i) := by
  induction i with
  | zero => simp [nibblePrefix, EvmAsm.Stateless.SpecRef.keyToNibbles]
  | succ k ih =>
    have hk : k ≤ srcBytes.length := by omega
    have hklt : k < srcBytes.length := by omega
    rw [nibblePrefix, ih hk, List.take_add_one,
      show srcBytes[k]? = some (srcBytes.getD k 0) from by
        rw [List.getElem?_eq_getElem hklt]
        rw [show srcBytes.getD k 0 = srcBytes[k]'hklt from by
          simp [List.getD, List.getElem?_eq_getElem hklt]]]
    simp only [Option.toList, EvmAsm.Stateless.SpecRef.keyToNibbles,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [nibblePair_eq]

/-- The routine's whole output, against the reference. -/
theorem bytesToNibblesBytes_eq_keyToNibbles (srcBytes : List (BitVec 8)) (len : Nat)
    (hlen : len ≤ srcBytes.length) :
    bytesToNibblesBytes srcBytes len
      = EvmAsm.Stateless.SpecRef.keyToNibbles (srcBytes.take len) := by
  rw [bytesToNibblesBytes, nibblePrefix_eq_keyToNibbles_take srcBytes len hlen]

/-! ## The flat whole-routine triple, derived by the adapter

    `bytesToNibblesFn_spec` is a structured SAsm `Fn.Spec`; callers compose against
    `cpsTripleWithin` at the linked guest address. `Fn.retSpecFlat` bridges the two, so the
    counted loop's invariant stays in the SAsm proof and is not re-litigated here.

    Unlike `bgv_u32le` this routine has a non-empty WRITABLE region, so the shape follows
    `Bn254Fq12SetOneSAsm.bnqZeroFlat_spec:133` — except that THREE argument registers are
    pinned in the precondition rather than one, hence a three-way split of the exposed
    file. `x11`/`x12` are not in the scratch list, so they must be handed back explicitly
    as `regOwn` in the post or the caller loses them. -/

def btnCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bytes_to_nibbles : Word) bytesToNibbles_prog

/-- The exposed registers other than the three ABI arguments. -/
def btnScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split3 (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) ** (.x12 ↦ᵣ vf .x12) **
          regAtomsOf vf btnScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [btnScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem args_notin_scratch :
    ∀ r ∈ btnScratch, r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) ∧ r ≠ (.x12 : Reg) := by
  decide

/-- ⭐ **`bytes_to_nibbles` at its linked guest address, against the reference.** The
    destination region ends up holding `keyToNibbles` of the consumed window — the
    reference function, not the routine's own accumulator. -/
theorem bytesToNibblesFlat_spec (ret src dst : Word) (len : Nat)
    (srcBytes orig : List (BitVec 8))
    (hlen : len ≤ srcBytes.length) (horig : orig.length = 2 * len)
    (hsrcOver : src.toNat + len < 2 ^ 64) (hdstOver : dst.toNat + 2 * len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + 2 * len ≤ src.toNat)
    (hwfR : (Region.mk src srcBytes).wf) (hwfW : RwRegion.wf ⟨dst, 2 * len⟩)
    (hsz : 4 * ((bytesToNibblesFn src dst len srcBytes orig).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bytesToNibblesFn src dst len srcBytes orig).body.steps + 1)
      (GuestAddrs.bytes_to_nibbles : Word) ret btnCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ dst) ** regOwns btnScratch ** bytesRegion dst orig **
        bytesRegion src srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ BitVec.ofNat 64 (2 * len)) **
        regOwn .x11 ** regOwn .x12 ** regOwns btnScratch **
        bytesRegion dst (EvmAsm.Stateless.SpecRef.keyToNibbles (srcBytes.take len)) **
        bytesRegion src srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns btnScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ BitVec.ofNat 64 len) **
        (.x12 ↦ᵣ dst) ** bytesRegion dst orig ** bytesRegion src srcBytes)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (bytesToNibblesFn src dst len srcBytes orig)
    (GuestAddrs.bytes_to_nibbles : Word)
    (bytesToNibblesFn_spec src dst len srcBytes orig hwfR hwfW
      (GuestAddrs.bytes_to_nibbles : Word))
    hsz ret halign
    (fun r => if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
              else if r = .x12 then dst else vf r)
    orig
    (show orig.length = 2 * len from horig)
    (by
      refine ⟨?_, ?_, ?_, rfl, hlen, horig, hsrcOver, hdstOver, hdisj, rfl⟩ <;>
        · rw [RegFile.get, if_neg (by decide)]
          simp
    )
    (fun _ _ _ h => h.2.2)
    (Q := (.x10 ↦ᵣ BitVec.ofNat 64 (2 * len)) ** regOwn .x11 ** regOwn .x12 **
      regOwns btnScratch **
      bytesRegion dst (EvmAsm.Stateless.SpecRef.keyToNibbles (srcBytes.take len)))
    (fun rf' ws' _ hpost' hp hh => by
      obtain ⟨hx10', hws', -⟩ := hpost'
      rw [hws', bytesToNibblesBytes_eq_keyToNibbles srcBytes len hlen] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split3,
        show rf' .x10 = BitVec.ofNat 64 (2 * len) from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10',
        show (bytesToNibblesFn src dst len srcBytes orig).rw.base = dst from rfl] at hh
      have hh2 := sepConj_mono_left
        (sepConj_mono_right (sepConj_mono
          (regIs_to_regOwn .x11 _)
          (sepConj_mono (regIs_to_regOwn .x12 _)
            (regAtomsOf_to_regOwns (fun r => rf' r) btnScratch)))) hp hh
      xperm_hyp hh2)
  rw [show (bytesToNibblesFn src dst len srcBytes orig).programRet
      (GuestAddrs.bytes_to_nibbles : Word) = bytesToNibbles_prog from rfl] at had
  have hadC := liftCode (cr' := btnCr) had (by unfold btnCr; code_mem)
  rw [show (bytesToNibblesFn src dst len srcBytes orig).rw.base = dst from rfl,
    show (bytesToNibblesFn src dst len srcBytes orig).region = Region.mk src srcBytes
      from rfl] at hadC
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split3,
    show (if (Reg.x10 : Reg) = .x10 then src else _) = src from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then src
          else if (Reg.x11 : Reg) = .x11 then BitVec.ofNat 64 len else _)
        = BitVec.ofNat 64 len from by rw [if_neg (by decide), if_pos rfl],
    show (if (Reg.x12 : Reg) = .x10 then src
          else if (Reg.x12 : Reg) = .x11 then BitVec.ofNat 64 len
          else if (Reg.x12 : Reg) = .x12 then dst else vf .x12) = dst from by
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl],
    regAtomsOf_congr (fun r => if r = .x10 then src
        else if r = .x11 then BitVec.ofNat 64 len
        else if r = .x12 then dst else vf r) vf btnScratch
      (fun r hr => by
        obtain ⟨h0, h1, h2⟩ := args_notin_scratch r hr
        show (if r = .x10 then src else if r = .x11 then BitVec.ofNat 64 len
              else if r = .x12 then dst else vf r) = vf r
        rw [if_neg h0, if_neg h1, if_neg h2])] at hadC
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hadC

/-! ## Non-vacuity pins -/

section Pins

#guard bytesToNibblesBytes [0xab, 0x04, 0xff] 3
  == EvmAsm.Stateless.SpecRef.keyToNibbles ([0xab, 0x04, 0xff] : List (BitVec 8))
-- nibble ORDER: high first. A swap would give [11,10,...] and fail here.
#guard bytesToNibblesBytes [(0xab : BitVec 8)] 1 == [(0x0a : BitVec 8), (0x0b : BitVec 8)]
-- extremes, and the `len < length` case (trailing bytes must be ignored)
#guard bytesToNibblesBytes [(0x00 : BitVec 8), (0xff : BitVec 8)] 2
  == EvmAsm.Stateless.SpecRef.keyToNibbles ([0x00, 0xff] : List (BitVec 8))
#guard bytesToNibblesBytes [(0x12 : BitVec 8), (0x34 : BitVec 8), (0x56 : BitVec 8)] 2
  == EvmAsm.Stateless.SpecRef.keyToNibbles ([0x12, 0x34] : List (BitVec 8))
#guard bytesToNibblesBytes [] 0 == EvmAsm.Stateless.SpecRef.keyToNibbles []
-- ⭐ the pins above would all pass if both sides were constantly empty; this one shows
-- the function is actually discriminating (pirapira's point on #11416).
#guard bytesToNibblesBytes [(0xab : BitVec 8)] 1 != bytesToNibblesBytes [(0xba : BitVec 8)] 1
#guard EvmAsm.Stateless.SpecRef.keyToNibbles ([0xab] : List (BitVec 8))
  != EvmAsm.Stateless.SpecRef.keyToNibbles ([0xba] : List (BitVec 8))

end Pins

end BytesToNibblesSAsm

end EvmAsm.Codegen
