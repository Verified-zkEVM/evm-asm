/-
  EvmAsm.Codegen.Programs.HpDecodeCompactBridge

  GH #11422 — the theorem `HpDecodeNibblesSAsm.lean`'s header says is owed:

      "the further link `hpDecode -> SpecRef.compact_to_nibbles` is still not
       stated as a theorem [...] the behaviour agrees, the proof does not exist yet."

  ⭐ WHAT WAS ACTUALLY MISSING, because it is much less than the issue's title
  suggests. #11422 lists three obligations, and the machine side of all three is
  already proven in `HpDecodeNibblesSAsmPaths.lean`:

    1. the odd-flag prepend  -> `pathD_spec` ("odd parity -- head nibble stored"),
       with `hdnC0_odd` / `hdnRes_some_odd` fixing the parity decode;
    2. the `is_leaf` flag    -> the `isl` cell is written
       `BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2)`, i.e. bit 1 of the head nibble;
    3. empty-input rejection -> `pathA_spec` ("len = 0 -- the first guard branches
       straight to the fail tail; nothing is written").

  And `hdnRes_eq_hpDecode` already ties the guest-exact mirror to `hpDecode`
  definitionally. So the chain `guest -> hdnRes -> hpDecode` is complete, and the
  ONE missing link is the last hop to the SpecRef port. That is what this file adds.

  ⚠️ THE DIVERGENCE THIS FILE DOES **NOT** HAVE TO HANDLE, recorded because a reader
  chasing #11422 will expect it: `hpDecode` used to reject a head nibble `>= 4`
  where `compact_to_nibbles` masks bits 2-3 away and accepts — the guest was
  STRICTER, a false-reject shape. GH #10528 closed that by making both sides mask.
  So the bridge below is a total agreement with no side condition, which is only
  true because that fix landed first; before #10528 this theorem was FALSE.

  METHOD. Two independent facts, neither interesting on its own:

    * the tails agree — `hpUnpackPairs = keyToNibbles`, which is pure composition:
      `nibblePrefix_eq_hpUnpackPairs` and `nibblePrefix_eq_keyToNibbles_take` are
      both stated as `nibblePrefix bs i = _ (bs.take i)`, so instantiating each at
      `i = bs.length` and collapsing `bs.take bs.length` joins them. Both halves
      already existed; only the join was absent.
    * the flags agree — `compact_to_nibbles` tests `first_nibble &&& 0x02` and
      `&&& 0x01` while `hpDecode` matches on `(b0.toNat / 16) % 4`. Both read the
      same two bits, and the byte-exhaustive `decide` below is what says so rather
      than a hand-rolled bit argument (the kernel's `Nat` is GMP-backed, so 256
      cases is cheap — see CLAUDE.md).
-/

import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsmPaths
import EvmAsm.Codegen.Programs.BytesToNibblesBridge
import EvmAsm.Stateless.SpecRef.IncrementalMpt

namespace EvmAsm.Codegen.HpDecodeNibblesSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.BytesToNibblesSAsm (nibblePrefix)

/-- ⭐ **The tails agree.** The guest mirror's pair-unpacking is the reference's
    `keyToNibbles`, obtained by joining two existing lemmas at `i = bs.length`.

    Both are phrased `nibblePrefix bs i = _ (bs.take i)`; neither mentions the
    other's right-hand side, which is why this join had to be written down. -/
theorem hpUnpackPairs_eq_keyToNibbles (bs : List (BitVec 8)) :
    EvmAsm.Evm64.hpUnpackPairs bs = EvmAsm.Stateless.SpecRef.keyToNibbles bs := by
  have h1 := nibblePrefix_eq_hpUnpackPairs bs bs.length le_rfl
  have h2 := EvmAsm.Codegen.BytesToNibblesSAsm.nibblePrefix_eq_keyToNibbles_take
    bs bs.length le_rfl
  rw [List.take_length] at h1 h2
  rw [← h1, h2]

/-- The head-nibble flag bits, read byte-exhaustively rather than argued.

    `compact_to_nibbles` masks `first_nibble` with `0x02`/`0x01`; `hpDecode`
    matches on `(b0.toNat / 16) % 4`. This says the two agree for every byte. -/
private theorem flag_bits (b0 : BitVec 8) :
    (decide ((b0.toNat / 16) &&& 0x02 = 0) = decide ((b0.toNat / 16) % 4 < 2)) ∧
    ((b0.toNat &&& 0x0F) = b0.toNat % 16) := by
  revert b0; decide

/-- ⭐ **The link #11422 asked for.** The reference port IS the guest mirror, up to
    the two representation differences and nothing else:

      * the tuple order — `hpDecode` returns `(isLeaf, nibbles)` where
        `compact_to_nibbles` returns `(nibbles, isLeaf)`;
      * the failure encoding — `none` against `throw (.witnessNodeMalformed …)`.

    Total: no hypothesis on `bs`. The empty case is a rejection on both sides, which
    is #11422's obligation 3 at the model level (`pathA_spec` is its machine half). -/
theorem compact_to_nibbles_eq_hpDecode (bs : List (BitVec 8)) :
    EvmAsm.Stateless.SpecRef.compact_to_nibbles bs
      = match EvmAsm.Evm64.hpDecode bs with
        | none => throw (.witnessNodeMalformed "compact_to_nibbles: empty input")
        | some (isLeaf, nibs) => pure (nibs, isLeaf) := by
  cases bs with
  | nil => rfl
  | cons b0 rest =>
    obtain ⟨hleaf, hlow⟩ := flag_bits b0
    -- The one representation gap simp does not close on its own: the reference
    -- shifts (`>>> 4`) where `hpDecode` divides (`/ 16`).
    have hsr : b0.toNat >>> 4 = b0.toNat / 16 := Nat.shiftRight_eq_div_pow _ _
    -- `hpDecode` branches on this value; `compact_to_nibbles` on the two bits.
    have hm : (b0.toNat / 16) % 4 = 0 ∨ (b0.toNat / 16) % 4 = 1 ∨
              (b0.toNat / 16) % 4 = 2 ∨ (b0.toNat / 16) % 4 = 3 := by omega
    simp only [EvmAsm.Stateless.SpecRef.compact_to_nibbles, EvmAsm.Evm64.hpDecode,
      hpUnpackPairs_eq_keyToNibbles, hlow, hsr]
    -- `hleaf` only fires once the match on `% 4` has reduced and exposed the
    -- `&&& 2` test, so it belongs in the per-case simp rather than above.
    rcases hm with h | h | h | h <;> simp only [h] <;>
      first
        | simp [hleaf, h, show b0.toNat / 16 % 2 = 0 from by omega]
        | simp [hleaf, h, show b0.toNat / 16 % 2 = 1 from by omega]

/-! ## Consuming the bridge in the caller-visible contract

    The theorem above is useful evidence only when the routine contract is
    stated through the port and then reconciled with the machine post.  These
    helpers are the port-shaped spelling of the five observable post pieces;
    the next theorem proves that spelling is exactly `hdnCallerPost`.

    PORT-FIDELITY CLAUSE TABLE (`incremental_mpt.py:859-889`,
    `SpecRef/IncrementalMpt.lean:71-89`):

    * input: Python reads `compact[0]` and rejects an empty byte string;
      `compact_to_nibbles_eq_hpDecode` proves the same success/error split;
    * flags: Python takes bits 1 and 0 of `compact[0] >>> 4`; `flag_bits`
      proves the machine's `% 4` branch reads exactly those bits;
    * odd path: Python prepends `compact[0] &&& 0x0f` exactly when bit 0 is
      set; `hpUnpackPairs_eq_keyToNibbles` plus the bridge theorem proves the
      same tuple path;
    * even path: Python omits the low head nibble and expands only the tail;
      the same tuple equality proves this without an extra hypothesis;
    * output order/error representation: the port returns `(nibbles,is_leaf)`
      or an error, while `hpDecode` returns `(is_leaf,nibbles)` or `none`;
      `compact_to_nibbles_eq_hpDecode` is the checked representation tie.

    No clause is left as a prose assumption.  The only assumptions in the
    machine theorem below are its ordinary ABI/resource preconditions. -/

private def hpPortNibs (bs : List (BitVec 8)) : List (BitVec 8) :=
  match EvmAsm.Stateless.SpecRef.compact_to_nibbles bs with
  | .ok (nibs, _) => nibs
  | .error _ => []

private def hpPortStatusW (bs : List (BitVec 8)) : Word :=
  match EvmAsm.Stateless.SpecRef.compact_to_nibbles bs with
  | .ok _ => 0
  | .error _ => 1

private def hpPortBufFinal (bs orig : List (BitVec 8)) : List (BitVec 8) :=
  setBytes orig 0 (hpPortNibs bs)

private def hpPortCntFinal (bs : List (BitVec 8)) (old : Word) : Word :=
  match EvmAsm.Stateless.SpecRef.compact_to_nibbles bs with
  | .ok (nibs, _) => BitVec.ofNat 64 nibs.length
  | .error _ => old

private def hpPortIslFinal (bs : List (BitVec 8)) (old : Word) : Word :=
  match EvmAsm.Stateless.SpecRef.compact_to_nibbles bs with
  | .ok (_, isLeaf) => if isLeaf then 1 else 0
  | .error _ => old

private theorem exceptPure {ε α : Type} (x : α) :
    (pure x : Except ε α) = .ok x := rfl

private theorem leafFlag (b0 : BitVec 8) :
    (b0.toNat / 16 % 4 = 0 →
      BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2) = (0 : Word)) ∧
    (b0.toNat / 16 % 4 = 1 →
      BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2) = (0 : Word)) ∧
    (b0.toNat / 16 % 4 = 2 →
      BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2) = (1 : Word)) ∧
    (b0.toNat / 16 % 4 = 3 →
      BitVec.ofNat 64 (b0.toNat / 16 / 2 % 2) = (1 : Word)) := by
  revert b0
  decide

def hdnPortPost (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (oldCnt oldIsl : Word) : Assertion :=
  (.x10 ↦ᵣ hpPortStatusW srcBytes) ** (.x11 ↦ᵣ BitVec.ofNat 64 srcBytes.length)
  ** (.x12 ↦ᵣ dst) ** (.x13 ↦ᵣ cnt) ** (.x14 ↦ᵣ isl)
  ** regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28
  ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
  ** (Reg.x0 ↦ᵣ (0 : Word))
  ** bytesRegion src srcBytes ** bytesRegion dst (hpPortBufFinal srcBytes bufOrig)
  ** (cnt ↦ₘ hpPortCntFinal srcBytes oldCnt)
  ** (isl ↦ₘ hpPortIslFinal srcBytes oldIsl)

theorem hdnPortPost_eq_hdnCallerPost (src dst cnt isl : Word)
    (srcBytes bufOrig : List (BitVec 8)) (oldCnt oldIsl : Word) :
    hdnPortPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl =
      hdnCallerPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl := by
  unfold hdnPortPost hdnCallerPost hpPortStatusW hpPortBufFinal hpPortNibs
    hpPortCntFinal hpPortIslFinal hdnStatusW hdnBufFinal hdnNibs hdnCntFinal
    hdnIslFinal hdnIslWritten hdnIsLeafW hdnRes
  cases srcBytes with
  | nil => rfl
  | cons b0 rest =>
    have hport := compact_to_nibbles_eq_hpDecode (b0 :: rest)
    rw [hport]
    have hm : b0.toNat / 16 % 4 = 0 ∨ b0.toNat / 16 % 4 = 1 ∨
        b0.toNat / 16 % 4 = 2 ∨ b0.toNat / 16 % 4 = 3 := by omega
    rcases hm with h0 | h1 | h2 | h3
    · have hleaf := (leafFlag b0).1 h0
      simp [hdnB0, hdnNibs, hdnRes, exceptPure, hleaf,
        EvmAsm.Evm64.hpDecode_cons_div0 b0 rest h0]
    · have hleaf := (leafFlag b0).2.1 h1
      simp [hdnB0, hdnNibs, hdnRes, exceptPure, hleaf,
        EvmAsm.Evm64.hpDecode_cons_div1 b0 rest h1]
    · have hleaf := (leafFlag b0).2.2.1 h2
      simp [hdnB0, hdnNibs, hdnRes, exceptPure, hleaf,
        EvmAsm.Evm64.hpDecode_cons_div2 b0 rest h2]
    · have hleaf := (leafFlag b0).2.2.2 h3
      simp [hdnB0, hdnNibs, hdnRes, exceptPure, hleaf,
        EvmAsm.Evm64.hpDecode_cons_div3 b0 rest h3]

/-- **Consumed port bridge.**  This is the same whole-routine contract as
    `hp_decode_nibbles_spec`, but its post is first stated through the
    `SpecRef.compact_to_nibbles` port.  The proof must use
    `hdnPortPost_eq_hdnCallerPost`; keeping that rewrite here prevents the
    port theorem from becoming decorative evidence beside an unrelated
    machine triple. -/
theorem hp_decode_nibbles_spec_ported (base sp0 ret : Word) (vals : Reg → Word)
    (src dst cnt isl : Word) (srcBytes bufOrig : List (BitVec 8))
    (v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl : Word)
    (hret : vals .x1 = ret)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + srcBytes.length < 2 ^ 64)
    (hsvalid : ∀ j, j < srcBytes.length →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hbuf : hdnC0 srcBytes + 2 * (srcBytes.length - 1) ≤ bufOrig.length)
    (hdalign : dst.toNat % 8 = 0) (hdover : dst.toNat + bufOrig.length < 2 ^ 64)
    (hdvalid : ∀ j, j < bufOrig.length →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (1 + hdnFrame.length + (30 + 11 * srcBytes.length)
        + hdnFrame.length + 1 + 1) base ret (hdnCr base)
      ((.x2 ↦ᵣ sp0) ** regsAt hdnFrame vals
        ** frameSlotsOwn hdnFrame (sp0 + signExtend12 (-48 : BitVec 12))
        ** hdnCallerPre src dst cnt isl srcBytes bufOrig
            v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl)
      ((.x2 ↦ᵣ sp0) ** regsAt hdnFrame vals
        ** frameSlotsSaved hdnFrame (sp0 + signExtend12 (-48 : BitVec 12)) vals
        ** hdnPortPost src dst cnt isl srcBytes bufOrig oldCnt oldIsl) := by
  rw [hdnPortPost_eq_hdnCallerPost]
  exact hp_decode_nibbles_spec base sp0 ret vals src dst cnt isl srcBytes bufOrig
    v5 v6 v7 v28 v29 v30 v31 oldCnt oldIsl hret halignRet hsalign hsover hsvalid
    hbuf hdalign hdover hdvalid

end EvmAsm.Codegen.HpDecodeNibblesSAsm
