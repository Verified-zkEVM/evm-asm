import EvmAsm.Codegen.Programs.ValidateParentHashLinkTop
import EvmAsm.Rv64.RLP.ItemDecodeForward

namespace EvmAsm.Codegen.ValidateParentHashLinkSpec
open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.Proofs
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Evm64.Terminating (copyIntoRegion copyIntoRegion_length)
/-! #12459 note: the legacy statement summary above mentions `hfieldAlign` and
    four dword loads.  The current code has no such premise: the claimed hash
    is copied byte-wise by `mset_memcpy`, and the source-window bound is now
    derived from each caller's slack/coverage facts and the successful decode.

    Concrete status-0 inhabitants for #12459.  The zero-filled child is a
    real mismatch against the digest of the four-byte parent; the second child
    carries that real digest.  Both use the complete `Success` relation. -/
private def vphlParentBytes0 : List (BitVec 8) := [0xaa, 0xbb, 0xcc, 0xdd]
private def vphlParentHash0 : List (BitVec 8) :=
  [0x40, 0xee, 0xd0, 0x32, 0x5a, 0x12, 0xc6, 0xc6,
   0xaf, 0x8d, 0xb2, 0xea, 0x05, 0x45, 0x0b, 0xfe,
   0x21, 0xd6, 0x34, 0x3b, 0x6f, 0xe9, 0x55, 0xbf,
   0xf6, 0x50, 0x45, 0xb6, 0x7d, 0x9d, 0x5f, 0xe6]
private def vphlChildZero : List (BitVec 8) :=
  [0xe1, 0xa0] ++ List.replicate 32 0 ++ List.replicate 9 0
private def vphlChildMatch : List (BitVec 8) :=
  [0xe1, 0xa0] ++ vphlParentHash0 ++ List.replicate 9 0

set_option maxRecDepth 8000 in
private theorem vphlParentHash0_is_digest :
    keccakBodyDigest vphlParentBytes0 0 4 = vphlParentHash0 := by decide

private theorem vphlChildZero_success :
    RlpListNthItemSAsm.Success vphlChildZero (0x30000 : Word) 34 0
      (2 : Word) (32 : Word) := by
  refine ⟨1, (0x30000 : Word) + 34, (0x30000 : Word) + 34,
    by exact .short 34 1 0xe1 (by decide) (by decide) (by decide) rfl (by decide),
    by
      refine .zero 1 ((0x30000 : Word) + 34) (32 : Word) (by
        apply EvmAsm.Rv64.RLP.rlpItemDecode_shortBytes_forward
          _ (0x30000 : Word) 1 34 0xa0 (List.replicate 32 0)
        all_goals decide),
    by decide⟩

private theorem vphlChildMatch_success :
    RlpListNthItemSAsm.Success vphlChildMatch (0x30000 : Word) 34 0
      (2 : Word) (32 : Word) := by
  refine ⟨1, (0x30000 : Word) + 34, (0x30000 : Word) + 34,
    by exact .short 34 1 0xe1 (by decide) (by decide) (by decide) rfl (by decide),
    by
      refine .zero 1 ((0x30000 : Word) + 34) (32 : Word) (by
        apply EvmAsm.Rv64.RLP.rlpItemDecode_shortBytes_forward
          _ (0x30000 : Word) 1 34 0xa0 vphlParentHash0
        all_goals decide),
    by decide⟩


private theorem vphl_valid_zone : ∀ (base n : Nat), 0x20 ≤ base →
    base + n ≤ 0x78000000 →
      isValidByteAccess (BitVec.ofNat 64 base + BitVec.ofNat 64 n) = true := by
  intro base n hbase hup
  have hb : base < 2 ^ 64 := by omega
  have hn : n < 2 ^ 64 := by omega
  have hs : base + n < 2 ^ 64 := by omega
  have hto : (BitVec.ofNat 64 base + BitVec.ofNat 64 n).toNat = base + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hs]
  simp only [isValidByteAccess, isValidMemAddr, hto, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  show ((0x20 ≤ base + n ∧ base + n ≤ 0x78000000) ∨
    (0x40000000 ≤ base + n ∧ base + n ≤ 0x40002000)) ∨
    (0xa0000000 ≤ base + n ∧ base + n ≤ 0xc0000000)
  exact Or.inl (Or.inl ⟨by omega, by omega⟩)

private def vphlStatus0Pre : Assertion :=
  ((.x2 ↦ᵣ (0x10000 : Word)) ** (.x1 ↦ᵣ (0x50000 : Word)) **
    (.x8 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ (0 : Word)) **
    (.x18 ↦ᵣ (0 : Word)) ** (.x19 ↦ᵣ (0 : Word)) **
    (.x20 ↦ᵣ (0 : Word)) ** (.x21 ↦ᵣ (0 : Word)) **
    (.x10 ↦ᵣ (0x20000 : Word)) **
    (.x11 ↦ᵣ (BitVec.ofNat 64 4)) ** (.x12 ↦ᵣ (0x30000 : Word)) **
    (.x13 ↦ᵣ (34 : Word)) ** (.x14 ↦ᵣ (0x40000 : Word)) **
    regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x15 ** regOwn .x16 **
    regOwn .x17 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
    (.x0 ↦ᵣ (0 : Word)) **
    memOwn ((0x10000 : Word) + signExtend12 (-48 : BitVec 12)) **
    memOwn ((0x10000 : Word) + signExtend12 (-48 : BitVec 12) + 8) **
    memOwn ((0x10000 : Word) + signExtend12 (-48 : BitVec 12) + 16) **
    memOwn ((0x10000 : Word) + signExtend12 (-48 : BitVec 12) + 24) **
    memOwn ((0x10000 : Word) + signExtend12 (-48 : BitVec 12) + 32) **
    memOwn ((0x10000 : Word) + signExtend12 (-48 : BitVec 12) + 40) **
    stackFree ((0x10000 : Word) + signExtend12 (-48 : BitVec 12)) 8 **
    bytesRegion (0x20000 : Word) vphlParentBytes0 **
    bytesRegion (0x30000 : Word) vphlChildZero **
    ((0x40000 : Word) ↦ₘ (0 : Word)) **
    (vphlOffsetAddr ↦ₘ (0 : Word)) **
    (vphlLengthAddr ↦ₘ (0 : Word)) **
    bytesRegion vphlClaimedAddr (List.replicate 32 (0 : BitVec 8)) **
    bytesRegion vphlComputedAddr (List.replicate 32 (0 : BitVec 8)) **
    bytesRegion vphlZk3 (List.replicate 200 (0 : BitVec 8)) ** empAssertion)

private def vphlStatus0Post : Assertion :=
  vphlRetPost (0x10000 : Word)
    ((0x10000 : Word) + signExtend12 (-48 : BitVec 12)) (0x50000 : Word)
    (0x40000 : Word) 0 0 0 0 0 0 (0x20000 : Word) (0x30000 : Word)
    vphlParentBytes0 vphlChildZero (List.replicate 32 (0 : BitVec 8))
    34 0 0 (List.replicate 200 (0 : BitVec 8)) ** empAssertion

set_option maxRecDepth 8000 in
theorem vphl_status0_inhabited :
    cpsTripleWithin (583 + keccakBodyFuel 0 4) vphlBase (0x50000 : Word) vphlCode
      vphlStatus0Pre vphlStatus0Post := by
  simpa only [vphlStatus0Pre, vphlStatus0Post] using
    (validate_parent_hash_link_spec_within
      (sp0 := (0x10000 : Word))
      (spC := (0x10000 : Word) + signExtend12 (-48 : BitVec 12))
      (retHdr := (0x50000 : Word))
      (parentBase := (0x20000 : Word))
      (parentLenW := BitVec.ofNat 64 4)
      (childBase := (0x30000 : Word))
      (childLenW := (34 : Word))
      (outPtr := (0x40000 : Word))
      (cs0 := 0) (cs1 := 0) (cs2 := 0) (cs3 := 0) (cs4 := 0) (v21 := 0)
      (oldOut := 0) (oldOffset := 0) (oldLen := 0)
      (parentBytes := vphlParentBytes0) (childBytes := vphlChildZero)
      (claimedOld := List.replicate 32 0)
      (childLen := 34) (N := 0) (rem := 4)
      (os := List.replicate 200 0) (F := empAssertion)
      (hret := by decide) (hspC := rfl) (hplenW := by decide)
      (hclenW := by decide) (hpover := by decide)
      (hpvalid := by
        intro k hk
        simp [vphlParentBytes0] at hk
        exact vphl_valid_zone 0x20000 k (by decide) (by omega))
      (hcalign := by decide)
      (hcslack := by simp [vphlChildZero])
      (hcover := by simp [vphlChildZero])
      (hcvalid := by
        intro k hk
        simp [vphlChildZero] at hk
        exact vphl_valid_zone 0x30000 k (by decide) (by omega))
      (hkeccakLen := by decide) (hrem_le := by decide)
      (hNbound := by decide) (hb8i := by decide) (hos := by decide)
      (hclaimedLen := by decide) (hF := pcFree_emp))

end EvmAsm.Codegen.ValidateParentHashLinkSpec
