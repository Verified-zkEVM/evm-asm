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
    is copied byte-wise by `mset_memcpy`, so `hfieldBound` is only the
    source-window bound required by that byte-copy contract.

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
  refine ⟨1, (0x30000 : Word) + 34, (0x30000 : Word) + 34, ?_, ?_, ?_⟩
  · exact .short 34 1 0xe1 (by decide) (by decide) (by decide) rfl (by decide)
  · refine .zero 1 ((0x30000 : Word) + 34) (32 : Word) ?_
    apply EvmAsm.Rv64.RLP.rlpItemDecode_shortBytes_forward
      _ (0x30000 : Word) 1 34 0xa0 (List.replicate 32 0)
    all_goals decide
  · decide

private theorem vphlChildMatch_success :
    RlpListNthItemSAsm.Success vphlChildMatch (0x30000 : Word) 34 0
      (2 : Word) (32 : Word) := by
  refine ⟨1, (0x30000 : Word) + 34, (0x30000 : Word) + 34, ?_, ?_, ?_⟩
  · exact .short 34 1 0xe1 (by decide) (by decide) (by decide) rfl (by decide)
  · refine .zero 1 ((0x30000 : Word) + 34) (32 : Word) ?_
    apply EvmAsm.Rv64.RLP.rlpItemDecode_shortBytes_forward
      _ (0x30000 : Word) 1 34 0xa0 vphlParentHash0
    all_goals decide
  · decide

private theorem vphlStatus0_hfieldBound (bs : List (BitVec 8))
    (hbs : bs = vphlChildZero ∨ bs = vphlChildMatch) :
    ∀ fo ln, RlpListNthItemSAsm.Success bs (0x30000 : Word) 34 0 fo ln →
      ln = (32 : Word) → fo.toNat + 32 ≤ bs.length := by
  rcases hbs with rfl | rfl
  · intro fo ln hs hln
    simp [vphlChildZero] at *
    unfold RlpListNthItemSAsm.Success at hs
    obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoff⟩ := hs
    cases hlist with
    | short b hbyte hnot hshort hcursor hlen =>
        subst cursorOff
        norm_num at hbyte hnot hshort hlen
        cases hnth with
        | zero off next len hitem =>
            rcases hitem with ⟨b', hb', hsingle | hshort' | hlong' | hlist' | hlonglist'⟩
            · simp_all
            · rcases hshort' with ⟨_, _, _, _, hnext, hlenItem⟩
              have hitemLen : BitVec.zeroExtend 64 b' - (128 : Word) = (32 : Word) := by
                calc
                  _ = ln := hlenItem.symm
                  _ = 32 := hln
              rw [hitemLen] at hnext
              have hnext' : next = (0x30000 : Word) + 34 := by
                calc
                  next = _ := hnext
                  _ = (0x30000 : Word) + 34 := by decide
              rw [hnext', hln] at hoff
              rw [hoff]
              decide
            · simp_all
            · simp_all
            · norm_num at hb'
              subst b'
              have hbad :
                  BitVec.ult (BitVec.zeroExtend 64 (129 : BitVec 8))
                    (0xf8 : Word) = true := by decide
              exact (hlonglist'.1 hbad).elim
    | long b first hbyte hlong hfirst hnz hminimal hcursor hlen =>
        norm_num at hbyte
        subst b
        norm_num [BitVec.ult] at hlong
        omega
  · intro fo ln hs hln
    simp [vphlChildMatch, vphlParentHash0] at *
    unfold RlpListNthItemSAsm.Success at hs
    obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoff⟩ := hs
    cases hlist with
    | short b hbyte hnot hshort hcursor hlen =>
        subst cursorOff
        norm_num at hbyte hnot hshort hlen
        cases hnth with
        | zero off next len hitem =>
            rcases hitem with ⟨b', hb', hsingle | hshort' | hlong' | hlist' | hlonglist'⟩
            · simp_all
            · rcases hshort' with ⟨_, _, _, _, hnext, hlenItem⟩
              have hitemLen : BitVec.zeroExtend 64 b' - (128 : Word) = (32 : Word) := by
                calc
                  _ = ln := hlenItem.symm
                  _ = 32 := hln
              rw [hitemLen] at hnext
              have hnext' : next = (0x30000 : Word) + 34 := by
                calc
                  next = _ := hnext
                  _ = (0x30000 : Word) + 34 := by decide
              rw [hnext', hln] at hoff
              rw [hoff]
              simp
            · simp_all
            · simp_all
            · norm_num at hb'
              subst b'
              have hbad :
                  BitVec.ult (BitVec.zeroExtend 64 (129 : BitVec 8))
                    (0xf8 : Word) = true := by decide
              exact (hlonglist'.1 hbad).elim
    | long b first hbyte hlong hfirst hnz hminimal hcursor hlen =>
        norm_num at hbyte
        subst b
        norm_num [BitVec.ult] at hlong
        omega

set_option maxRecDepth 8000 in
example : True := by
  have valid_zone : ∀ (base n : Nat), 0x20 ≤ base → base + n ≤ 0x78000000 →
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
  let run_status0 (childBytes : List (BitVec 8))
      (hcslack : 34 + 9 ≤ childBytes.length)
      (hcover : (0x30000 : Word).toNat + childBytes.length < 2 ^ 64)
      (hcvalid : ∀ k, k < childBytes.length →
        isValidByteAccess ((0x30000 : Word) + BitVec.ofNat 64 k) = true)
      (hfieldBound : ∀ fo ln,
        RlpListNthItemSAsm.Success childBytes (0x30000 : Word) 34 0 fo ln →
        ln = (32 : Word) → fo.toNat + 32 ≤ childBytes.length) :=
    validate_parent_hash_link_spec_within
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
      (parentBytes := vphlParentBytes0) (childBytes := childBytes)
      (claimedOld := List.replicate 32 0)
      (childLen := 34) (N := 0) (rem := 4)
      (os := List.replicate 200 0) (F := empAssertion)
      (hret := by decide) (hspC := rfl) (hplenW := by decide)
      (hclenW := by decide) (hpalign := by decide) (hpover := by decide)
      (hpvalid := by
        intro k hk
        simp [vphlParentBytes0] at hk
        exact valid_zone 0x20000 k (by decide) (by omega))
      (hcalign := by decide) (hcslack := hcslack) (hcover := hcover)
      (hcvalid := hcvalid) (hfieldBound := hfieldBound)
      (houtAlign := by decide) (houtValid := by decide)
      (hkeccakLen := by decide) (hrem_le := by decide)
      (hNbound := by decide) (hb8i := by decide) (hos := by decide)
      (hclaimedLen := by decide) (hF := pcFree_emp)
  have _hzero := run_status0 vphlChildZero
    (by simp [vphlChildZero]) (by simp [vphlChildZero])
    (by
      intro k hk
      simp [vphlChildZero] at hk
      exact valid_zone 0x30000 k (by decide) (by omega))
    (vphlStatus0_hfieldBound vphlChildZero (Or.inl rfl))
  have _hmatch := run_status0 vphlChildMatch
    (by simp [vphlChildMatch, vphlParentHash0])
    (by simp [vphlChildMatch, vphlParentHash0])
    (by
      intro k hk
      simp [vphlChildMatch, vphlParentHash0] at hk
      exact valid_zone 0x30000 k (by decide) (by omega))
    (vphlStatus0_hfieldBound vphlChildMatch (Or.inr rfl))
  have _h := validate_parent_hash_link_spec_within
    (sp0 := (0x10000 : Word))
    (spC := (0x10000 : Word) + signExtend12 (-48 : BitVec 12))
    (retHdr := (0x50000 : Word))
    (parentBase := (0x20000 : Word))
    (parentLenW := BitVec.ofNat 64 4)
    (childBase := (0x30000 : Word))
    (childLenW := (3 : Word))
    (outPtr := (0x40000 : Word))
    (cs0 := 0) (cs1 := 0) (cs2 := 0) (cs3 := 0) (cs4 := 0) (v21 := 0)
    (oldOut := 0) (oldOffset := 0) (oldLen := 0)
    (parentBytes := [0xaa, 0xbb, 0xcc, 0xdd])
    (childBytes := [0xc2, 0x81, 0x01] ++ List.replicate 9 0)
    (claimedOld := List.replicate 32 0)
    (childLen := 3) (N := 0) (rem := 4)
    (os := List.replicate 200 0) (F := empAssertion)
    (hret := by decide)
    (hspC := rfl)
    (hplenW := by decide)
    (hclenW := by decide)
    (hpalign := by decide)
    (hpover := by decide)
    (hpvalid := by
      intro k hk
      norm_num at hk
      exact valid_zone 0x20000 k (by decide) (by omega))
    (hcalign := by decide)
    (hcslack := by decide)
    (hcover := by decide)
    (hcvalid := by
      intro k hk
      norm_num at hk
      exact valid_zone 0x30000 k (by decide) (by omega))
    (hfieldBound := by
      intro fo ln hs hln
      unfold RlpListNthItemSAsm.Success at hs
      obtain ⟨cursorOff, endPtr, next, hlist, hnth, hoff⟩ := hs
      cases hlist with
      | short b hbyte hnot hshort hcursor hlen =>
          subst cursorOff
          norm_num at hbyte hnot hshort hlen
          cases hnth with
          | zero off next len hitem =>
              rcases hitem with ⟨b', hb', hsingle | hshort' | hlong' | hlist' | hlonglist'⟩
              · simp_all
              · simp_all
              · simp_all
              · simp_all
              · norm_num at hb'
                subst b'
                have hbad :
                    BitVec.ult (BitVec.zeroExtend 64 (129 : BitVec 8))
                      (0xf8 : Word) = true := by decide
                exact (hlonglist'.1 hbad).elim
      | long b first hbyte hlong hfirst hnz hminimal hcursor hlen =>
          norm_num at hbyte
          subst b
          norm_num [BitVec.ult] at hlong
          omega)
    (houtAlign := by decide)
    (houtValid := by decide)
    (hkeccakLen := by decide)
    (hrem_le := by decide)
    (hNbound := by decide)
    (hb8i := by decide)
    (hos := by decide)
    (hclaimedLen := by decide)
    (hF := pcFree_emp)
  trivial

end EvmAsm.Codegen.ValidateParentHashLinkSpec
