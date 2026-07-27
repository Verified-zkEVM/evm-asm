/-
  EvmAsm.Rv64.SailEquiv.MemReduce

  Bare-mode memory reduction for the Sail golden-model equivalence (Phase 2).

  Pure little-endian reassembly identities connecting Sail's byte memory to the
  dword view of `StateRel.mem_agree`: `byte_ext`, `packDword_extractByte`,
  `reconstructDword_eq_packDword`, `reconstructDword_of_bytes`, and
  `reconstructDword_congr`. These feed the load capstones (`VmemReduction.lean` /
  `VmemReductionLoads.lean`) and the store-side `mem_agree` rebuild bridges
  (`VmemReductionStores.lean`) — the lemmas that discharged the load/store stubs
  `MemProofs.lean` used to carry (that file is now a historical anchor; no stubs
  remain).
-/

import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.ByteOps

open Sail

namespace EvmAsm.Rv64.SailEquiv

open EvmAsm.Rv64

/-- **Byte extensionality** for 64-bit words: two words agreeing on all eight
    bytes are equal. -/
theorem byte_ext {x y : Word} (h : ∀ i : Fin 8, extractByte x i.val = extractByte y i.val) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hlt : j / 8 < 8 := by omega
  have hb := congrArg (fun b : BitVec 8 => b.getLsbD (j % 8)) (h ⟨j / 8, hlt⟩)
  have hidx : j / 8 * 8 + j % 8 = j := by omega
  have hm : j % 8 < 8 := by omega
  simpa [extractByte, hidx, hm] using hb

/-- Packing a word's own bytes (little-endian) recovers the word. -/
theorem packDword_extractByte (v : Word) :
    packDword (fun i => extractByte v i.val) = v := by
  apply byte_ext
  intro i
  exact extractByte_packDword

/-- `reconstructDword` is `packDword` over the eight bytes read from the map. -/
theorem reconstructDword_eq_packDword (mem : Std.ExtHashMap Nat (BitVec 8)) (addr : Nat) :
    reconstructDword mem addr = packDword (fun i : Fin 8 => mem.getD (addr + i.val) 0) := rfl

/-- **Little-endian reassembly.** If the eight bytes at `addr … addr+7` are the
    byte slices of a 64-bit value `v` (byte `i` = `extractByte v i`), then
    `reconstructDword` recovers `v`.  This bridges Sail's byte-level memory
    (written little-endian by `writeBytes`) to the dword view of
    `StateRel.mem_agree`. -/
theorem reconstructDword_of_bytes
    (mem : Std.ExtHashMap Nat (BitVec 8)) (addr : Nat) (v : Word)
    (h : ∀ i, i < 8 → mem.getD (addr + i) 0 = extractByte v i) :
    reconstructDword mem addr = v := by
  rw [reconstructDword_eq_packDword]
  have hfun : (fun i : Fin 8 => mem.getD (addr + i.val) 0)
      = (fun i : Fin 8 => extractByte v i.val) := by
    funext i; exact h i.val i.isLt
  rw [hfun, packDword_extractByte]

/-- `reconstructDword` reads only the eight bytes at `addr … addr+7`, so it is
    invariant under changes elsewhere.  Combined with the 8-aligned disjointness of
    distinct doublewords, this is how an aligned store leaves *other* dwords'
    `mem_agree` untouched. -/
theorem reconstructDword_congr
    {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {addr : Nat}
    (h : ∀ i, i < 8 → mem'.getD (addr + i) 0 = mem.getD (addr + i) 0) :
    reconstructDword mem' addr = reconstructDword mem addr := by
  rw [reconstructDword_eq_packDword, reconstructDword_eq_packDword]
  congr 1
  funext i
  exact h i.val i.isLt

end EvmAsm.Rv64.SailEquiv
