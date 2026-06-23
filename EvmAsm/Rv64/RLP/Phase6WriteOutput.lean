/-
  EvmAsm.Rv64.RLP.Phase6WriteOutput

  EL.3 / Phase 6 — the pipeline's output half. The `write_output` syscall appends
  `readBytes ptr size` (byte-granular) to the public output; the decoder leaves its result as a
  `bytesRegion` (dword-packed). This file bridges them — `readBytes_of_bytesRegion`: when
  `bytesRegion base bs` holds, `readBytes base bs.length = bs` — the keystone connecting the
  decoder's output region to what `write_output` emits.
-/

import EvmAsm.Rv64.RLP.Phase6ReadDecode

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/-- **A byte read from a held `bytesRegion`.** When `bytesRegion regionBase bs ** R` holds in `s`
    (region dword-aligned, byte `i` in range, no address overflow), `s.getByte (regionBase + i)`
    is `bs[i]` — the `holdsFor`-level byte read underlying `bytesRegion_lbu_within`. -/
theorem getByte_of_bytesRegion (regionBase : Word) (bs : List (BitVec 8)) (i : Nat)
    (R : Assertion) (s : MachineState)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (h : (bytesRegion regionBase bs ** R).holdsFor s) :
    s.getByte (regionBase + BitVec.ofNat 64 i) = bs[i]'hi := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, _hf, _hr, heq⟩ := bytesRegion_dword_at regionBase bs (i / 8) hq
  rw [heq] at h
  have hmem : s.getMem (regionBase + BitVec.ofNat 64 (8 * (i / 8)))
      = packBytes ((bs.drop (8 * (i / 8))).take 8) :=
    holdsFor_memIs_getMem (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left h)))
  unfold MachineState.getByte
  rw [alignToDword_add_ofNat_of_aligned halign hover, hmem,
      byteOffset_add_ofNat_of_aligned halign hover,
      extractByte_packBytes _ _ (by omega)
        (by rw [List.length_take, List.length_drop]; omega),
      List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- **`readBytes` reads back a held `bytesRegion`.** When `bytesRegion base bs ** R` holds in `s`
    (dword-aligned, no overflow), reading `bs.length` bytes from `base` returns `bs`. The bridge
    connecting the decoder's `bytesRegion` output to what `write_output` (which uses `readBytes`)
    emits. -/
theorem readBytes_of_bytesRegion (base : Word) (bs : List (BitVec 8)) (R : Assertion)
    (s : MachineState)
    (halign : base.toNat % 8 = 0) (hover : base.toNat + bs.length < 2 ^ 64)
    (h : (bytesRegion base bs ** R).holdsFor s) :
    s.readBytes base bs.length = bs := by
  -- Generalised: reading `n` bytes from offset `off` returns `(bs.drop off).take n`.
  have key : ∀ n off, off + n ≤ bs.length →
      s.readBytes (base + BitVec.ofNat 64 off) n = (bs.drop off).take n := by
    intro n
    induction n with
    | zero => intro off _; simp
    | succ m ih =>
      intro off hoff
      have hoff' : off < bs.length := by omega
      rw [MachineState.readBytes_succ,
          getByte_of_bytesRegion base bs off R s halign hoff' (by omega) h,
          show (base + BitVec.ofNat 64 off) + 1 = base + BitVec.ofNat 64 (off + 1) from by bv_omega,
          ih (off + 1) (by omega),
          List.drop_eq_getElem_cons hoff', List.take_succ_cons]
  have := key bs.length 0 (by omega)
  rwa [show base + BitVec.ofNat 64 0 = base from by bv_omega, List.drop_zero,
      List.take_length] at this

end EvmAsm.Rv64.RLP
