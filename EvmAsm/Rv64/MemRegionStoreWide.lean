/-
  EvmAsm.Rv64.MemRegionStoreWide

  `bytesRegion_sw_at_within`: the `SW` counterpart of `bytesRegion_sb_within`
  (MemRegionStore). Storing a 32-bit word at a 4-aligned byte index `i` of a
  region turns `bytesRegion regionBase bs` into
  `bytesRegion regionBase (setBytes bs i (word32Bytes (v.truncate 32)))`.

  The algebraic core (`packBytes_setBytes_word32`) and the paired region split
  (`bytesRegion_dword_at_setBytes`) both already live in `MemRegionWriteWide`;
  this module only ties them to `generic_sw_spec_within`, exactly as
  `bytesRegion_sb_within` ties `packBytes_set` to `generic_sb_spec_within`.

  Unlike the `SB` lemma the address is given as `ptr + signExtend12 offset`
  with a caller-supplied identification `hptr`, because the callers that need
  this (little-endian offset headers such as EIP-7685 SSZ `ExecutionRequests`)
  write several words off ONE base register with different immediates.
-/

module

public import EvmAsm.Rv64.MemRegionStore
public import EvmAsm.Rv64.MemRegionWriteWide
public import EvmAsm.Rv64.WordOps

@[expose] public section

namespace EvmAsm.Rv64

/-- **`SW` writes the 4 bytes at index `i` of the region.** `i` is 4-aligned
    and the region base is dword-aligned, so the payload never straddles two
    dword cells. -/
theorem bytesRegion_sw_at_within (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word)
    (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i)
    (hi : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hvalid : isValidMemAccess (regionBase + BitVec.ofNat 64 i) = true) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegion regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
       bytesRegion regionBase (setBytes bs i (word32Bytes (v_data.truncate 32)))) := by
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have hr4 : 4 ∣ i % 8 := Nat.dvd_mod_iff (by norm_num) |>.mpr hi4
  have hr8 : i % 8 + 4 ≤ 8 := by
    obtain ⟨m, hm⟩ := hr4
    have : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
    omega
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes regionBase bs (word32Bytes (v_data.truncate 32))
      (i / 8) (i % 8) (by simp [word32Bytes]) (by simpa using hr8)
      (by simpa [hi_eq] using hi)
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have hvalid' : isValidMemAccess (ptr + signExtend12 offset) = true := by
    rw [hptr]; exact hvalid
  have sw := generic_sw_spec_within rs1 rs2 ptr v_data offset base
    dwordAddr wordVal halign' hvalid'
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 + 4 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_setBytes_word32 _ (i % 8) (v_data.truncate 32)
    hr4 hr8 hchunk_len] at sw
  rw [heq, show setBytes bs i (word32Bytes (v_data.truncate 32))
      = setBytes bs (8 * (i / 8) + i % 8) (word32Bytes (v_data.truncate 32))
      from by rw [hi_eq], heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sw)

end EvmAsm.Rv64
