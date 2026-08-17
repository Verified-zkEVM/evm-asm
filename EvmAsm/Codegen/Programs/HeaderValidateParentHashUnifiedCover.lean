/-
  EvmAsm.Codegen.Programs.HeaderValidateParentHashUnifiedCover

  Full-premise cover witnesses for the unified
  `header_validate_parent_hash_spec_within` dispatcher (see
  HeaderValidateParentHashUnified.lean).  Each cover instantiates EVERY
  static premise of the dispatcher simultaneously -- the leaf extraction
  premises, `hOutLen`, and the full 17-premise keccak envelope -- with
  LIVE (nonzero) data, so no arm of the unified post is reachable only
  in the large:

  * `…_extract_fail_cover`: a non-list prefix (`0x10 < 0xc0`) makes the
    leaf extract fail, exercising the status-1 arm.
  * `…_match_cover`: `thisBytes` carries the REAL
    `keccakBodyDigest [0xaa,0xbb,0xcc,0xdd] 0 4` as field 0, exercising
    the status-0 arm with nonzero digest bytes.
  * `…_mismatch2_cover`: field 0 is the real digest with BYTE 16 (the
    low byte of dword 2) flipped -- dwords 0/1 still equal, dword 2
    differs -- exercising the NEW round-1..3 mismatch machinery (the
    coverage gap that motivated the unified theorem) rather than the
    round-0 arm.

  All keccak-valued evaluations run under `set_option maxRecDepth 8000`
  (kernel `decide` on closed terms only; no `native_decide` /
  `bv_decide`).
-/

import EvmAsm.Codegen.Programs.HeaderValidateParentHashUnified

namespace EvmAsm.Codegen.HeaderValidateParentHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

/-! ## Zone helpers

    `isValidMemAddr` is the concrete three-zone check (`Word.lean`);
    these helpers discharge it once so the covers below reduce to
    `decide`/`omega` side conditions. -/

private theorem valid_byte_zone (base n : Nat) (hbase : 0x20 ≤ base)
    (hup : base + n ≤ 0x78000000) :
    isValidByteAccess (BitVec.ofNat 64 base + BitVec.ofNat 64 n) = true := by
  have hb : base < 2 ^ 64 := by omega
  have hnb : n < 2 ^ 64 := by omega
  have hsum : base + n < 2 ^ 64 := by omega
  have hn : (BitVec.ofNat 64 base + BitVec.ofNat 64 n).toNat = base + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt hsum]
  simp only [isValidByteAccess, isValidMemAddr, hn, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  show ((0x20 ≤ base + n ∧ base + n ≤ 0x78000000) ∨
      (0x40000000 ≤ base + n ∧ base + n ≤ 0x40002000)) ∨
    (0xa0000000 ≤ base + n ∧ base + n ≤ 0xc0000000)
  exact Or.inl (Or.inl ⟨by omega, by omega⟩)

private theorem zk3_toNat_eq :
    (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat = 0xa3a4c0e0 := by
  have hmod : 0xa3a4c0e0 % 2 ^ 64 = 0xa3a4c0e0 :=
    Nat.mod_eq_of_lt (by decide)
  simp only [GuestAddrs.zk3_state, BitVec.toNat_ofNat, hmod]

private theorem valid_byte_ram (n : Nat) (hn : n ≤ 199) :
    isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 n) = true := by
  have hnb : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmod : (0xa3a4c0e0 + n) % 2 ^ 64 = 0xa3a4c0e0 + n :=
    Nat.mod_eq_of_lt (by omega)
  have hn' : (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 n).toNat
      = 0xa3a4c0e0 + n := by
    rw [BitVec.toNat_add, zk3_toNat_eq, BitVec.toNat_ofNat, hnb, hmod]
  simp only [isValidByteAccess, isValidMemAddr, hn', Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  show ((0x20 ≤ 0xa3a4c0e0 + n ∧ 0xa3a4c0e0 + n ≤ 0x78000000) ∨
      (0x40000000 ≤ 0xa3a4c0e0 + n ∧ 0xa3a4c0e0 + n ≤ 0x40002000)) ∨
    (0xa0000000 ≤ 0xa3a4c0e0 + n ∧ 0xa3a4c0e0 + n ≤ 0xc0000000)
  exact Or.inr ⟨by omega, by omega⟩

private theorem valid_mem_ram (n : Nat) (hn : n ≤ 199) :
    isValidMemAddr (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 n) = true := by
  have hnb : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmod : (0xa3a4c0e0 + n) % 2 ^ 64 = 0xa3a4c0e0 + n :=
    Nat.mod_eq_of_lt (by omega)
  have hn' : (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 n).toNat
      = 0xa3a4c0e0 + n := by
    rw [BitVec.toNat_add, zk3_toNat_eq, BitVec.toNat_ofNat, hnb, hmod]
  simp only [isValidMemAddr, hn', Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  show ((0x20 ≤ 0xa3a4c0e0 + n ∧ 0xa3a4c0e0 + n ≤ 0x78000000) ∨
      (0x40000000 ≤ 0xa3a4c0e0 + n ∧ 0xa3a4c0e0 + n ≤ 0x40002000)) ∨
    (0xa0000000 ≤ 0xa3a4c0e0 + n ∧ 0xa3a4c0e0 + n ≤ 0xc0000000)
  exact Or.inr ⟨by omega, by omega⟩

private theorem zk3_toNat_add_lt (n : Nat) (h : 0xa3a4c0e0 + n < 2 ^ 64) :
    (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + n < 2 ^ 64 := by
  rw [zk3_toNat_eq]; omega

private theorem cursor30000 :
    keccakAbsorbCursor (0x30000 : Word) 0 = (0x30000 : Word) := by
  decide

private theorem w30000_toNat : ((0x30000 : Word)).toNat = 0x30000 := by
  decide

private theorem cursor30000_toNat_add_lt (n : Nat) (h : 0x30000 + n < 2 ^ 64) :
    (keccakAbsorbCursor (0x30000 : Word) 0).toNat + n < 2 ^ 64 := by
  rw [cursor30000, w30000_toNat]; omega

private theorem valid_byte_cursor (n : Nat) (hn : n ≤ 199) :
    isValidByteAccess
        (keccakAbsorbCursor (0x30000 : Word) 0 + BitVec.ofNat 64 n) = true := by
  rw [cursor30000]
  exact valid_byte_zone 0x30000 n (by omega) (by omega)

/-! ## Extract-fail cover (status 1) -/

set_option maxRecDepth 8000 in
/-- Every dispatcher premise holds simultaneously on a non-list-prefix
    input, and the leaf extract genuinely fails (status ≠ 0). -/
theorem header_validate_parent_hash_extract_fail_cover :
    ∃ (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
        (_vals : Reg → Word) (_v20 : Word)
        (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
        (os : List (BitVec 8)) (F : Assertion),
      F.pcFree ∧
      ret &&& ~~~(1 : Word) = ret ∧
      spC = sp0 + signExtend12 (-32 : BitVec 12) ∧
      thisBytes.length = thisLen.toNat ∧
      3 ≤ thisBytes.length ∧
      C0.length = 32 ∧
      thisPtr.toNat % 8 = 0 ∧
      thisPtr.toNat + thisBytes.length ≤ 2 ^ 64 ∧
      (∀ k, k < thisBytes.length →
        isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) ∧
      (headersParentHash_out thisBytes C0).length = 32 ∧
      parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem) ∧
      parentBytes.length = keccakAbsorbStep * N + rem ∧
      rem ≤ 135 ∧
      os.length = 200 ∧
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0 ∧
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64 ∧
      keccakAbsorbStep * N + rem < 2 ^ 63 ∧
      rem < 2 ^ 64 ∧
      (keccakAbsorbCursor parentPtr N).toNat % 8 = 0 ∧
      (∀ n, n < rem →
        (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true ∧
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true ∧
      (∀ j, j < 200 →
        isValidMemAddr (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) ∧
      headersParentHash_status thisBytes ≠ 0 := by
  refine ⟨(0x10000 : Word), 0x10000 + signExtend12 (-32 : BitVec 12), (0x50000 : Word),
    (0x20000 : Word), (BitVec.ofNat 64 4 : Word), (0x30000 : Word), (BitVec.ofNat 64 4 : Word),
    (fun _ => (0 : Word)), (0 : Word),
    (0x10 :: 0x00 :: 0x00 :: 0x00 :: ([] : List (BitVec 8))),
    (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))),
    (List.replicate 32 0), 0, 4, (List.replicate 200 0), empAssertion,
    ⟨pcFree_emp, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
      (by
        intro k hk
        have hlen :
            (0x10 :: 0x00 :: 0x00 :: 0x00 :: ([] : List (BitVec 8))).length = 4 := by
          decide
        rw [hlen] at hk
        exact valid_byte_zone 0x20000 k (by decide) (by omega)),
      by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide,
      by rw [cursor30000]; decide,
      fun n _hn => zk3_toNat_add_lt (4 - (n + 1)) (by omega),
      fun n _hn => cursor30000_toNat_add_lt (4 - (n + 1)) (by omega),
      fun n _hn => valid_byte_ram (4 - (n + 1)) (by omega),
      fun n _hn => valid_byte_cursor (4 - (n + 1)) (by omega),
      by decide, by decide,
      fun j hj => valid_mem_ram j (by omega),
      by decide⟩⟩

/-! ## Match cover (status 0) -/

set_option maxRecDepth 8000 in
/-- Every dispatcher premise holds with field 0 = the REAL digest of a
    four-byte parent (`N = 0`, `rem = 4`), and all four dwords of the
    extracted field equal the digest -- the status-0 arm guard. -/
theorem header_validate_parent_hash_match_cover :
    ∃ (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
        (_vals : Reg → Word) (_v20 : Word)
        (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
        (os : List (BitVec 8)) (F : Assertion),
      F.pcFree ∧
      ret &&& ~~~(1 : Word) = ret ∧
      spC = sp0 + signExtend12 (-32 : BitVec 12) ∧
      thisBytes.length = thisLen.toNat ∧
      3 ≤ thisBytes.length ∧
      C0.length = 32 ∧
      thisPtr.toNat % 8 = 0 ∧
      thisPtr.toNat + thisBytes.length ≤ 2 ^ 64 ∧
      (∀ k, k < thisBytes.length →
        isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) ∧
      (headersParentHash_out thisBytes C0).length = 32 ∧
      parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem) ∧
      parentBytes.length = keccakAbsorbStep * N + rem ∧
      rem ≤ 135 ∧
      os.length = 200 ∧
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0 ∧
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64 ∧
      keccakAbsorbStep * N + rem < 2 ^ 63 ∧
      rem < 2 ^ 64 ∧
      (keccakAbsorbCursor parentPtr N).toNat % 8 = 0 ∧
      (∀ n, n < rem →
        (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true ∧
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true ∧
      (∀ j, j < 200 →
        isValidMemAddr (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) ∧
      headersParentHash_status thisBytes = 0 ∧
      ∀ q, q < 4 →
        dwordAt (headersParentHash_out thisBytes C0) q =
          dwordAt (keccakBodyDigest parentBytes N rem) q := by
  refine ⟨(0x10000 : Word), 0x10000 + signExtend12 (-32 : BitVec 12), (0x50000 : Word),
    (0x20000 : Word), (BitVec.ofNat 64 85 : Word), (0x30000 : Word), (BitVec.ofNat 64 4 : Word),
    (fun _ => (0 : Word)), (0 : Word),
    (0xf4 :: 0xa0 ::
      (keccakBodyDigest (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4 ++
        List.replicate 51 0x11)),
    (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))),
    (List.replicate 32 0), 0, 4, (List.replicate 200 0), empAssertion,
    ⟨pcFree_emp, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
      (by
        intro k hk
        have hlen :
            (0xf4 :: 0xa0 ::
              (keccakBodyDigest (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4 ++
                List.replicate 51 0x11)).length = 85 := by
          decide
        rw [hlen] at hk
        exact valid_byte_zone 0x20000 k (by decide) (by omega)),
      by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide,
      by rw [cursor30000]; decide,
      fun n _hn => zk3_toNat_add_lt (4 - (n + 1)) (by omega),
      fun n _hn => cursor30000_toNat_add_lt (4 - (n + 1)) (by omega),
      fun n _hn => valid_byte_ram (4 - (n + 1)) (by omega),
      fun n _hn => valid_byte_cursor (4 - (n + 1)) (by omega),
      by decide, by decide,
      fun j hj => valid_mem_ram j (by omega),
      by decide,
      (by
        intro q _hq
        have hout : headersParentHash_out
            (0xf4 :: 0xa0 ::
              (keccakBodyDigest (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4 ++
                List.replicate 51 0x11))
            (List.replicate 32 0) =
            keccakBodyDigest (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4 := by
          decide
        rw [hout])⟩⟩

/-! ## Mismatch-at-round-2 cover (status 2, exercising the new rounds) -/

set_option maxRecDepth 8000 in
/-- Every dispatcher premise holds with field 0 = the real digest with
    BYTE 16 (the low byte of dword 2) flipped: dwords 0 and 1 still
    match, dword 2 differs.  This is the guard shape of the
    `hvphUnifiedMismatch2` arm -- the coverage gap (rounds 1-3) that the
    unified theorem closes. -/
theorem header_validate_parent_hash_mismatch2_cover :
    ∃ (sp0 spC ret thisPtr thisLen parentPtr parentLen : Word)
        (_vals : Reg → Word) (_v20 : Word)
        (thisBytes parentBytes C0 : List (BitVec 8)) (N rem : Nat)
        (os : List (BitVec 8)) (F : Assertion),
      F.pcFree ∧
      ret &&& ~~~(1 : Word) = ret ∧
      spC = sp0 + signExtend12 (-32 : BitVec 12) ∧
      thisBytes.length = thisLen.toNat ∧
      3 ≤ thisBytes.length ∧
      C0.length = 32 ∧
      thisPtr.toNat % 8 = 0 ∧
      thisPtr.toNat + thisBytes.length ≤ 2 ^ 64 ∧
      (∀ k, k < thisBytes.length →
        isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true) ∧
      (headersParentHash_out thisBytes C0).length = 32 ∧
      parentLen = BitVec.ofNat 64 (keccakAbsorbStep * N + rem) ∧
      parentBytes.length = keccakAbsorbStep * N + rem ∧
      rem ≤ 135 ∧
      os.length = 200 ∧
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0 ∧
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64 ∧
      keccakAbsorbStep * N + rem < 2 ^ 63 ∧
      rem < 2 ^ 64 ∧
      (keccakAbsorbCursor parentPtr N).toNat % 8 = 0 ∧
      (∀ n, n < rem →
        (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        (keccakAbsorbCursor parentPtr N).toNat + (rem - (n + 1)) < 2 ^ 64) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
      (∀ n, n < rem →
        isValidByteAccess
          (keccakAbsorbCursor parentPtr N + BitVec.ofNat 64 (rem - (n + 1))) = true) ∧
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true ∧
      isValidByteAccess (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true ∧
      (∀ j, j < 200 →
        isValidMemAddr (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) ∧
      headersParentHash_status thisBytes = 0 ∧
      dwordAt (headersParentHash_out thisBytes C0) 0 =
        dwordAt (keccakBodyDigest parentBytes N rem) 0 ∧
      dwordAt (headersParentHash_out thisBytes C0) 1 =
        dwordAt (keccakBodyDigest parentBytes N rem) 1 ∧
      dwordAt (headersParentHash_out thisBytes C0) 2 ≠
        dwordAt (keccakBodyDigest parentBytes N rem) 2 := by
  refine ⟨(0x10000 : Word), 0x10000 + signExtend12 (-32 : BitVec 12), (0x50000 : Word),
    (0x20000 : Word), (BitVec.ofNat 64 85 : Word), (0x30000 : Word), (BitVec.ofNat 64 4 : Word),
    (fun _ => (0 : Word)), (0 : Word),
    (0xf4 :: 0xa0 ::
      ((keccakBodyDigest (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4).take 16 ++
        (0xFF :: (((keccakBodyDigest
            (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4).drop 17 ++
          List.replicate 51 0x11))))),
    (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))),
    (List.replicate 32 0), 0, 4, (List.replicate 200 0), empAssertion,
    ⟨pcFree_emp, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
      (by
        intro k hk
        have hlen :
            (0xf4 :: 0xa0 ::
              ((keccakBodyDigest (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4).take 16 ++
                (0xFF :: (((keccakBodyDigest
                    (0xaa :: 0xbb :: 0xcc :: 0xdd :: ([] : List (BitVec 8))) 0 4).drop 17 ++
                  List.replicate 51 0x11))))).length = 85 := by
          decide
        rw [hlen] at hk
        exact valid_byte_zone 0x20000 k (by decide) (by omega)),
      by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide,
      by rw [cursor30000]; decide,
      fun n _hn => zk3_toNat_add_lt (4 - (n + 1)) (by omega),
      fun n _hn => cursor30000_toNat_add_lt (4 - (n + 1)) (by omega),
      fun n _hn => valid_byte_ram (4 - (n + 1)) (by omega),
      fun n _hn => valid_byte_cursor (4 - (n + 1)) (by omega),
      by decide, by decide,
      fun j hj => valid_mem_ram j (by omega),
      by decide, by decide, by decide⟩⟩

end EvmAsm.Codegen.HeaderValidateParentHashSpec
