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

import EvmAsm.Codegen.Programs.HpDecodeNibblesSAsm
import EvmAsm.Codegen.Programs.BytesToNibblesBridge
import EvmAsm.Stateless.SpecRef.IncrementalMpt

namespace EvmAsm.Codegen.HpDecodeNibblesSAsm

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

end EvmAsm.Codegen.HpDecodeNibblesSAsm
