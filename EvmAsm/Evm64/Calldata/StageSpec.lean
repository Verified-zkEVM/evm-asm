/-
  EvmAsm.Evm64.Calldata.StageSpec

  The verified staging step for the ARENA-FREE CALLDATALOAD (bead
  evm-asm-t1iqb, phase B): the ≤32-byte copy-with-zero-fill loop that
  materializes the CALLDATALOAD window into the aligned staging buffer.
  This is the copy-loop verification the CALLDATACOPY slice deferred
  (`CopySpec.lean` proved only the preamble).

  Option-1 source model (unaligned aliased calldata): the calldata is a
  byte-slice of the aligned parent-memory / input arena.  The precondition
  carries `bytesRegion memBase memBytes` with `memBase % 8 = 0`, the calldata
  pointer `cdp = memBase + cdByteOff`, and the calldata bytes are
  `data = (memBytes.drop cdByteOff).take len`.  The loop reads calldata byte
  `pos` at aligned index `cdByteOff + pos` and writes the aligned staging
  buffer `bytesRegion buf …`, so both memory accesses are 8-aligned dword
  cells even though `cdp` itself is unaligned.
-/

import EvmAsm.Evm64.Calldata.StageProgram
import EvmAsm.Evm64.Calldata.StageWindow
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/-- The byte the loop copies at window index `i`: the real calldata byte at
    the normalized source position, or zero out of bounds. -/
theorem stage_copy_byte_eq
    (data memBytes : List (BitVec 8)) (cdByteOff normOff len i : Nat)
    (h_fits : cdByteOff + len ≤ memBytes.length)
    (h_data : data = (memBytes.drop cdByteOff).take len)
    (h_i : normOff + i < len) :
    (memBytes[cdByteOff + normOff + i]'(by omega)) =
      callDataByte data (normOff + i) := by
  subst h_data
  rw [callDataByte_of_lt (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- Buffer content after `i` window bytes have been copied: the copied prefix
    of `copyBytes` followed by the still-original suffix of the buffer. -/
def stageBufContent (copyBytes origBuf : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  copyBytes.take i ++ origBuf.drop i

theorem stageBufContent_length (copyBytes origBuf : List (BitVec 8)) (i : Nat)
    (h_cb : copyBytes.length = 32) (h_ob : origBuf.length = 64) (h_i : i ≤ 32) :
    (stageBufContent copyBytes origBuf i).length = 64 := by
  simp only [stageBufContent, List.length_append, List.length_take,
    List.length_drop, h_cb, h_ob]
  omega

/-- Writing `copyBytes[i]` at index `i` advances the buffer content from the
    `i`-prefix to the `(i+1)`-prefix. -/
theorem stageBufContent_set (copyBytes origBuf : List (BitVec 8)) (i : Nat)
    (v : BitVec 8) (h_i : i < copyBytes.length) (h_i2 : i < origBuf.length)
    (h_v : v = copyBytes[i]) :
    (stageBufContent copyBytes origBuf i).set i v
      = stageBufContent copyBytes origBuf (i + 1) := by
  apply List.ext_getElem
  · simp only [stageBufContent, List.length_set, List.length_append,
      List.length_take, List.length_drop]
    omega
  · intro j hj1 _
    have hlen : (stageBufContent copyBytes origBuf i).length = origBuf.length := by
      simp only [stageBufContent, List.length_append, List.length_take,
        List.length_drop]; omega
    rw [List.length_set, hlen] at hj1
    by_cases h_eq : j = i
    · subst h_eq
      rw [List.getElem_set_self]
      simp only [stageBufContent]
      rw [List.getElem_append_left (by rw [List.length_take]; omega),
          List.getElem_take]
      exact h_v
    · rw [List.getElem_set_ne (Ne.symm h_eq)]
      -- both sides agree away from i
      simp only [stageBufContent]
      by_cases h_lt : j < i
      · rw [List.getElem_append_left (by rw [List.length_take]; omega),
            List.getElem_append_left (by rw [List.length_take]; omega),
            List.getElem_take, List.getElem_take]
      · have h_gt : i < j := by omega
        have ht1 : (List.take i copyBytes).length = i := by
          rw [List.length_take]; omega
        have ht2 : (List.take (i + 1) copyBytes).length = i + 1 := by
          rw [List.length_take]; omega
        rw [List.getElem_append_right (by rw [ht1]; omega),
            List.getElem_append_right (by rw [ht2]; omega),
            List.getElem_drop, List.getElem_drop]
        congr 1
        omega

end Calldata
end EvmAsm.Evm64
