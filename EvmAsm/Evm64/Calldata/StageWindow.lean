/-
  EvmAsm.Evm64.Calldata.StageWindow

  Pure read-side bridge for the ARENA-FREE (staged) CALLDATALOAD (bead
  evm-asm-t1iqb, phase B).  The staging step materializes the 32-byte
  CALLDATALOAD window into a small fixed buffer as
  `stagedWindowBytes data offset = callDataCopyBytes data offset 32` — the
  window bytes with out-of-bounds positions already zero-filled — and the
  verified window ladder is then re-run over that buffer at offset 0.

  This file proves the two pure facts the composition needs:

  * `calldataloadOutputLimb_stagedWindow` — reading window quarter `w` of the
    staged buffer at offset 0 recovers the same output limb the ladder would
    produce over the real calldata at `offset` (the buffer holds exactly the
    window bytes, so `offLo = 0` in-bounds reads reproduce them).
  * `callDataLoadWord_getLimbN_{0,1,2,3}` — each output-limb quarter over the
    real calldata at a raw offset `N` is a limb of `callDataLoadWord data N`
    (keyed on the raw `Nat` offset, with NO upper-limb-zero hypothesis: the
    staging normalization has already folded the ≥ 2^64 case into zeros).

  Together with `stagedWindowBytes_eq_callDataCopyBytes` these turn the
  window ladder's `calldataloadOutputLimb (stagedWindowBytes ..) 0 w` output
  into `(callDataLoadWord data N).getLimbN j`.
-/

import EvmAsm.Evm64.Calldata.LoadWindowArm
import EvmAsm.Evm64.Calldata.LoadWindowWord

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/-- The 32-byte window content staged into the buffer for CALLDATALOAD at
    calldata offset `off`: the window bytes with out-of-bounds positions
    zero-filled (`callDataByte`), always length 32. -/
def stagedWindowBytes (data : List (BitVec 8)) (off : Nat) : List (BitVec 8) :=
  callDataCopyBytes data off 32

@[simp] theorem stagedWindowBytes_length (data : List (BitVec 8)) (off : Nat) :
    (stagedWindowBytes data off).length = 32 := by
  simp [stagedWindowBytes]

theorem stagedWindowBytes_eq_callDataCopyBytes
    (data : List (BitVec 8)) (off : Nat) :
    stagedWindowBytes data off = callDataCopyBytes data off 32 := rfl

/-- Reading window byte `j < 32` of the staged buffer recovers the calldata
    byte `off + j` (zero past the end). -/
theorem callDataByte_stagedWindow
    (data : List (BitVec 8)) (off j : Nat) (h : j < 32) :
    callDataByte (stagedWindowBytes data off) j = callDataByte data (off + j) := by
  have hlen : j < (stagedWindowBytes data off).length := by
    rw [stagedWindowBytes_length]; exact h
  rw [callDataByte_of_lt hlen]
  exact callDataCopyBytes_get h

/-- The window output limb over the staged buffer at offset 0 equals the
    output limb over the real calldata at `off`.  `w ∈ {0, 8, 16, 24}`. -/
theorem calldataloadOutputLimb_stagedWindow
    (data : List (BitVec 8)) (off w : Nat) (h_w_le : w ≤ 24) :
    calldataloadOutputLimb (stagedWindowBytes data off) 0 w =
      calldataloadOutputLimb data off w := by
  unfold calldataloadOutputLimb
  simp only [Nat.zero_add]
  rw [callDataByte_stagedWindow data off w (by omega),
      callDataByte_stagedWindow data off (w + 1) (by omega),
      callDataByte_stagedWindow data off (w + 2) (by omega),
      callDataByte_stagedWindow data off (w + 3) (by omega),
      callDataByte_stagedWindow data off (w + 4) (by omega),
      callDataByte_stagedWindow data off (w + 5) (by omega),
      callDataByte_stagedWindow data off (w + 6) (by omega),
      callDataByte_stagedWindow data off (w + 7) (by omega)]
  simp only [Nat.add_assoc]

/-! ## Output limbs are the `callDataLoadWord` limbs (keyed on the raw offset)

Unlike `LoadSpec.calldataload_out_limb{0,1,2,3}` (which relate
`offsetWord.getLimbN 0` to the word under an upper-limbs-zero hypothesis),
these are keyed directly on the raw `Nat` offset `N`, so they need no
side condition — the staging has already normalized the ≥ 2^64 case. -/

/-- Bridge: the window word decoded from the raw offset `N` (via `loadArgs`
    of any word whose `toNat` is `N`) is `callDataLoadWord data N`. -/
private theorem window_word_eq (data : List (BitVec 8)) (offset : EvmWord) :
    calldataLoadWindowOutputWordFromArgs data (CallDataLoadArgs.loadArgs offset) =
      callDataLoadWord data offset.toNat := by
  rw [calldataLoadWindowOutputWordFromArgs_eq_loadedWordFromArgs,
    CallDataLoadArgs.loadedWordFromArgs_eq, CallDataLoadArgs.loadArgs_offset]

theorem callDataLoadWord_getLimbN_0 (data : List (BitVec 8)) (offset : EvmWord) :
    (callDataLoadWord data offset.toNat).getLimbN 0 =
      calldataloadOutputLimb data offset.toNat 24 := by
  rw [← window_word_eq data offset,
    getLimbN_calldataLoadWindowOutputWordFromArgs_0]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

theorem callDataLoadWord_getLimbN_1 (data : List (BitVec 8)) (offset : EvmWord) :
    (callDataLoadWord data offset.toNat).getLimbN 1 =
      calldataloadOutputLimb data offset.toNat 16 := by
  rw [← window_word_eq data offset,
    getLimbN_calldataLoadWindowOutputWordFromArgs_1]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

theorem callDataLoadWord_getLimbN_2 (data : List (BitVec 8)) (offset : EvmWord) :
    (callDataLoadWord data offset.toNat).getLimbN 2 =
      calldataloadOutputLimb data offset.toNat 8 := by
  rw [← window_word_eq data offset,
    getLimbN_calldataLoadWindowOutputWordFromArgs_2]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

theorem callDataLoadWord_getLimbN_3 (data : List (BitVec 8)) (offset : EvmWord) :
    (callDataLoadWord data offset.toNat).getLimbN 3 =
      calldataloadOutputLimb data offset.toNat 0 := by
  rw [← window_word_eq data offset,
    getLimbN_calldataLoadWindowOutputWordFromArgs_3]
  unfold calldataloadOutputLimb
  simp only [CallDataLoadArgs.windowByteFromArgs_eq,
    CallDataLoadArgs.loadArgs_offset, Nat.add_assoc, Nat.reduceAdd]

end Calldata
end EvmAsm.Evm64
