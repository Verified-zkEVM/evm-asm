/-
  EvmAsm.Codegen.Programs.HeadersParentHashSpec

  Whole-routine machine triple for the emitted guest routine
  `headers_parent_hash` (K17, `headersParentHash_prog` in
  `EvmAsm/Codegen/Programs/HeadersKeccak.lean`, linked at
  `GuestAddrs.headers_parent_hash`).  This is the sole undischarged
  residual of conjunct 11 of `validate_header` (issue #12346): the
  `header_validate_parent_hash` arms are proved against a named premise
  `nH` standing for this routine's triple; this file replaces that
  premise with the real thing.

  ## What the routine does (34 instructions)

  RLP-walk an encoded header to its `parent_hash` field:
    * byte 0 must be an RLP long-string prefix `0xf8 + lol` with
      `lol ∈ {1, 2}` (i.e. `0xf8 ≤ b0 ≤ 0xf9`), or any short-form prefix
      `0xc0 ≤ b0 < 0xf8` (list, payload starts immediately);
    * after skipping the `skip = lol + 1` (resp. `1`) prefix bytes, the
      remaining length must be at least 33 and the next byte must be
      `0xa0` (32-byte string prefix for `parent_hash`);
    * on success the 32 bytes at `skip + 1` are copied to the output
      buffer and `a0 := 0`; on any parse failure `a0 := 1` and the
      output buffer is unchanged.

  ## Contract shape

  Per the `AGENTS.md` spec-design convention the statement carries only
  static preconditions (pointers, lengths, alignment, memory validity);
  the outcome (`headersParentHash_ok`) appears only in the
  postcondition, which pins the status register and the exact output
  bytes as functions of the input.  Clobbered caller-saved scratch
  registers `t0/t1/t2/t3` (`x5/x6/x7/x28`) are owned (valued) in the
  precondition and returned as `regOwn` in the postcondition; `a1/a2`
  (`x11/x12`) are likewise returned as `regOwn` havoc ownership, because
  the routine clobbers `a1` (`sub`/`addi`) and the caller's
  `mv a1, s1` at the call site needs write-ownership of it.
-/

import EvmAsm.Codegen.Programs.HeadersKeccak
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Linked base address of `headers_parent_hash`. -/
abbrev hphBase : Word := BitVec.ofNat 64 GuestAddrs.headers_parent_hash

/-- Output buffer address (the `hvph_claimed` 32-byte slot). -/
abbrev hphClaimed : Word := BitVec.ofNat 64 GuestAddrs.hvph_claimed

/-- Code requirement for the whole 34-instruction routine. -/
abbrev hphCode : CodeReq := CodeReq.ofProg hphBase headersParentHash_prog

/-- The routine is 34 instructions (the length fact the caller's
    code-extent arguments consume). -/
theorem headersParentHash_length : headersParentHash_prog.length = 34 := by
  decide

/-- First header byte (the RLP prefix), as a natural number. -/
def headersParentHash_b0 (thisBytes : List (BitVec 8)) : Nat :=
  (thisBytes[0]?.getD 0).toNat

/-- Prefix length walked by the routine: `1` for short-form prefixes
    (`b0 < 0xf8`), `lol + 1 = b0 - 246` for long-form ones.  Only
    meaningful when `0xc0 ≤ b0 ≤ 0xf9`; on other inputs the routine
    fails before the value is used. -/
def headersParentHash_skip (b0 : Nat) : Nat :=
  if b0 < 248 then 1 else b0 - 246

/-- Success condition, as a function of the header bytes:
    RLP prefix in range, at least `skip + 33` bytes remain, and the
    `parent_hash` field prefix is `0xa0`. -/
def headersParentHash_ok (thisBytes : List (BitVec 8)) : Bool :=
  decide (192 ≤ headersParentHash_b0 thisBytes) &&
  decide (headersParentHash_b0 thisBytes ≤ 249) &&
  decide (headersParentHash_skip (headersParentHash_b0 thisBytes) + 33 ≤ thisBytes.length) &&
  (thisBytes[headersParentHash_skip (headersParentHash_b0 thisBytes)]?.getD 0 == 0xa0)

/-- Return status in `a0`: `0` on success, `1` on RLP parse failure. -/
def headersParentHash_status (thisBytes : List (BitVec 8)) : Word :=
  if headersParentHash_ok thisBytes then 0 else 1

/-- Output buffer contents on return: the 32 copied `parent_hash` bytes
    on success, the previous contents unchanged on failure. -/
def headersParentHash_out (thisBytes claimedBytes : List (BitVec 8)) : List (BitVec 8) :=
  if headersParentHash_ok thisBytes then
    (thisBytes.drop (headersParentHash_skip (headersParentHash_b0 thisBytes) + 1)).take 32
  else claimedBytes

/-- Loop-invariant output window: after `i` copy iterations the output
    buffer holds the first `i` copied `parent_hash` bytes followed by the
    untouched tail of the original contents. -/
def hphWindow (thisBytes claimedBytes : List (BitVec 8)) (skip i : Nat) :
    List (BitVec 8) :=
  (thisBytes.drop (skip + 1)).take i ++ claimedBytes.drop i

theorem hphWindow_zero (thisBytes claimedBytes : List (BitVec 8)) (skip : Nat) :
    hphWindow thisBytes claimedBytes skip 0 = claimedBytes := by
  simp [hphWindow]

theorem hphWindow_length (thisBytes claimedBytes : List (BitVec 8)) (skip i : Nat)
    (hsrc : skip + 1 + i ≤ thisBytes.length) (hclaimed : claimedBytes.length = 32)
    (hi : i ≤ 32) :
    (hphWindow thisBytes claimedBytes skip i).length = 32 := by
  simp only [hphWindow, List.length_append, List.length_take, List.length_drop]
  omega

theorem hphWindow_full (thisBytes claimedBytes : List (BitVec 8)) (skip : Nat)
    (hclaimed : claimedBytes.length = 32) :
    hphWindow thisBytes claimedBytes skip 32
      = (thisBytes.drop (skip + 1)).take 32 := by
  simp [hphWindow, hclaimed]

/-- One copy-iteration step of the window: writing byte `i` extends the
    copied prefix by one. -/
theorem hphWindow_set (b c : List (BitVec 8)) (s i : Nat)
    (hdroplen : i < (b.drop (s + 1)).length)
    (hclaimed : c.length = 32) (hi : i < 32) :
    (hphWindow b c s i).set i ((b.drop (s + 1))[i]) = hphWindow b c s (i + 1) := by
  have hdlen : ((b.drop (s + 1)).take i).length = i := by
    rw [List.length_take]; omega
  have htake : (b.drop (s + 1)).take (i + 1)
      = (b.drop (s + 1)).take i ++ [(b.drop (s + 1))[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hdroplen]; rfl
  have htakei : ((b.drop (s + 1)).take i ++ c.drop i).take i
      = (b.drop (s + 1)).take i := by
    rw [List.take_append, hdlen, show i - i = 0 from by omega, List.take_zero,
      List.append_nil]
    exact List.take_of_length_le (le_of_eq hdlen)
  have hdropi : ((b.drop (s + 1)).take i ++ c.drop i).drop (i + 1)
      = c.drop (i + 1) := by
    rw [List.drop_append, hdlen,
      List.drop_eq_nil_of_le (show ((b.drop (s + 1)).take i).length ≤ i + 1 from
        by rw [hdlen]; omega),
      show i + 1 - i = 1 from by omega, List.drop_drop, List.nil_append]
  simp only [hphWindow]
  rw [List.set_eq_take_append_cons_drop,
    if_pos (show i < ((b.drop (s + 1)).take i ++ c.drop i).length by
      rw [List.length_append, hdlen, List.length_drop]; omega),
    htakei, hdropi, htake, List.append_assoc]
  rfl

/-- `toNat` of the output buffer base. -/
theorem hphClaimed_toNat : hphClaimed.toNat = GuestAddrs.hvph_claimed := by
  decide

/-- The claimed output slot: 32 valid bytes in RAM. -/
theorem hphClaimed_valid (i : Nat) (hi : i < 32) :
    isValidByteAccess (hphClaimed + BitVec.ofNat 64 i) = true := by
  have hv : GuestAddrs.hvph_claimed = 2755176224 := by decide
  have hto : (hphClaimed + BitVec.ofNat 64 i).toNat
      = GuestAddrs.hvph_claimed + i := by
    rw [BitVec.toNat_add, hphClaimed_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show GuestAddrs.hvph_claimed + i < 2 ^ 64 by omega)]
  rw [isValidByteAccess_eq, isValidMemAddr_eq, hto]
  exact Bool.or_eq_true_iff.2 (Or.inr (Bool.and_eq_true_iff.2
    ⟨decide_eq_true (by simp only [Rv64.RAM_MEM_START]; omega),
     decide_eq_true (by simp only [Rv64.RAM_MEM_END]; omega)⟩))

theorem hphClaimed_over (i : Nat) (hi : i < 32) :
    hphClaimed.toNat + i < 2 ^ 64 := by
  have hv : GuestAddrs.hvph_claimed = 2755176224 := by decide
  rw [hphClaimed_toNat, hv]; omega

theorem hphClaimed_align : hphClaimed.toNat % 8 = 0 := by
  rw [hphClaimed_toNat]; decide

/-- Loaded-byte/word conversions for the prefix byte. -/
theorem hphB0_lt_256 (thisBytes : List (BitVec 8)) :
    headersParentHash_b0 thisBytes < 256 := by
  simp only [headersParentHash_b0]
  exact BitVec.isLt _

/-- `zeroExtend 64` of the first byte equals `ofNat 64` of `b0`. -/
theorem hphB0_word (thisBytes : List (BitVec 8)) (h0 : 0 < thisBytes.length) :
    (thisBytes[0]'h0).zeroExtend 64
      = BitVec.ofNat 64 (headersParentHash_b0 thisBytes) := by
  apply BitVec.eq_of_toNat_eq
  have hb : headersParentHash_b0 thisBytes = (thisBytes[0]'h0).toNat := by
    simp only [headersParentHash_b0, List.getElem?_eq_getElem h0,
      Option.getD_some]
  rw [hb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The `0xa0` comparison in word form. -/
theorem hphByte160_eq (b : BitVec 8) :
    (b.zeroExtend 64 = (160 : Word)) ↔ b = (0xa0 : BitVec 8) := by
  constructor
  · intro h
    have htn := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, show (160 : Word).toNat = 160 from by decide,
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from by
        have := BitVec.isLt b; omega)] at htn
    apply BitVec.eq_of_toNat_eq
    rw [htn]; decide
  · intro h
    subst h
    rfl

/-- `PCFree` for byte regions (needed for framing). -/
instance (regionBase : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion regionBase bs) :=
  ⟨bytesRegion_pcFree _ _⟩

/-- Loop counter below the bound is nonzero-mod-2^64 in word form. -/
private theorem hphOfNat_ne_32 (i : Nat) (hi : i < 32) :
    BitVec.ofNat 64 i ≠ (32 : Word) := by
  intro h
  have htn := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    show (32 : Word).toNat = 32 from by decide] at htn
  omega

/-- One copy-loop iteration (idx 23..28, `hphBase+92 → hphBase+116`):
    write `thisBytes[skip+1+i]` into output slot `i`, bump the counter. -/
private theorem hph_copy_body_spec_within
    (retHdr thisPtr w11 : Word) (v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8)) (skip i : Nat)
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsi : skip + 1 + i < thisBytes.length)
    (hsover : thisPtr.toNat + (skip + 1 + i) < 2 ^ 64)
    (hsvalid : isValidByteAccess (thisPtr + BitVec.ofNat 64 (skip + 1 + i)) = true)
    (hclaimed : claimedBytes.length = 32) (hi : i < 32) :
    cpsTripleWithin 6 (hphBase + 92) (hphBase + 116) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x5 ↦ᵣ BitVec.ofNat 64 i) ** (.x6 ↦ᵣ (32 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip i) **
       bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x5 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x6 ↦ᵣ (32 : Word)) **
       (.x7 ↦ᵣ (hphClaimed + BitVec.ofNat 64 i)) **
       (.x28 ↦ᵣ (thisBytes[skip + 1 + i]'hsi).zeroExtend 64) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip (i + 1)) **
       bytesRegion thisPtr thisBytes) := by
  have h23 := addi_spec_gen_within .x7 .x10 v7 (thisPtr + BitVec.ofNat 64 skip)
    (1 : BitVec 12) (hphBase + 92) (by decide)
  rw [show (thisPtr + BitVec.ofNat 64 skip) + signExtend12 (1 : BitVec 12)
      = thisPtr + BitVec.ofNat 64 (skip + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide];
        bv_omega] at h23
  have h24 := add_spec_gen_rd_eq_rs1_within .x7 .x5
    (thisPtr + BitVec.ofNat 64 (skip + 1)) (BitVec.ofNat 64 i) (hphBase + 96) (by decide)
  rw [show thisPtr + BitVec.ofNat 64 (skip + 1) + BitVec.ofNat 64 i
      = thisPtr + BitVec.ofNat 64 (skip + 1 + i) from by bv_omega] at h24
  have h25 := bytesRegion_lbu_within .x28 .x7 thisPtr v28 (hphBase + 100)
    thisBytes (skip + 1 + i) (by decide) hsalign hsi hsover hsvalid
  have h26 := add_spec_gen_within .x7 .x12 .x5 hphClaimed (BitVec.ofNat 64 i)
    (thisPtr + BitVec.ofNat 64 (skip + 1 + i)) (hphBase + 104) (by decide)
  have hwlen : i < (hphWindow thisBytes claimedBytes skip i).length := by
    rw [hphWindow_length thisBytes claimedBytes skip i (by omega) hclaimed (by omega)]
    exact hi
  have h27 := bytesRegion_sb_within .x7 .x28 hphClaimed
    ((thisBytes[skip + 1 + i]'hsi).zeroExtend 64) (hphBase + 108)
    (hphWindow thisBytes claimedBytes skip i) i hphClaimed_align hwlen
    (hphClaimed_over i hi) (hphClaimed_valid i hi)
  rw [show ((thisBytes[skip + 1 + i]'hsi).zeroExtend 64).truncate 8
      = thisBytes[skip + 1 + i]'hsi from by simp] at h27
  have hdl : i < (thisBytes.drop (skip + 1)).length := by
    rw [List.length_drop]; omega
  have hset : (hphWindow thisBytes claimedBytes skip i).set i
      (thisBytes[skip + 1 + i]'hsi)
      = hphWindow thisBytes claimedBytes skip (i + 1) := by
    have heq : thisBytes[skip + 1 + i]'hsi = (thisBytes.drop (skip + 1))[i]'hdl :=
      List.getElem_drop' hsi
    rw [heq]; exact hphWindow_set thisBytes claimedBytes skip i hdl hclaimed hi
  rw [hset] at h27
  have h28 := addi_spec_gen_same_within .x5 (BitVec.ofNat 64 i) (1 : BitVec 12)
    (hphBase + 112) (by decide)
  rw [show BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12)
      = BitVec.ofNat 64 (i + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide];
        bv_omega] at h28
  runBlock h23 h24 h25 h26 h27 h28

private theorem hphAddr_beq_taken : hphBase + 88 + signExtend13 (32 : BitVec 13) = hphBase + 120 := by
  rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]; bv_omega

private theorem hphAddr_beq_fall : (hphBase + 88 : Word) + 4 = hphBase + 92 := by bv_omega

private theorem hphAddr_jal_back : (hphBase + 116) + signExtend21 (-32 : BitVec 21) = hphBase + 84 := by
  rw [show signExtend21 (-32 : BitVec 21) = (0xFFFFFFFFFFFFFFE0 : Word) from by decide]
  bv_omega

/-- The copy loop (idx 21..29, entry `hphBase+84`): `m = 32 - i` iterations
    remaining, then the success exit (`a0 := 0`, return). -/
private theorem hph_loop_spec_within
    (retHdr : Word) (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (thisPtr w11 : Word) (skip : Nat) (v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length →
      isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hclaimed : claimedBytes.length = 32)
    (m i : Nat) (hi : i + m = 32)
    (hskiplen : skip + 1 + i + m ≤ thisBytes.length) :
    cpsTripleWithin (9 * m + 4) (hphBase + 84) retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x5 ↦ᵣ BitVec.ofNat 64 i) ** (.x6 ↦ᵣ v6) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip i) **
       bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (0 : Word)) **
       regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
       (.x11 ↦ᵣ w11) ** regOwn .x12 **
       bytesRegion hphClaimed ((thisBytes.drop (skip + 1)).take 32) **
       bytesRegion thisPtr thisBytes) := by
  have hmono21 : ∀ a i', CodeReq.singleton (hphBase + 84) (.LI .x6 (32 : Word)) a = some i'
      → hphCode a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 21
      (hphBase + 84) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono22 : ∀ a i', CodeReq.singleton (hphBase + 88) (.BEQ .x5 .x6 (32 : BitVec 13)) a = some i'
      → hphCode a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 22
      (hphBase + 88) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono29 : ∀ a i', CodeReq.singleton (hphBase + 116) (.JAL .x0 (-32 : BitVec 21)) a = some i'
      → hphCode a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 29
      (hphBase + 116) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono30 : ∀ a i', CodeReq.singleton (hphBase + 120) (.LI .x10 (0 : Word)) a = some i'
      → hphCode a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 30
      (hphBase + 120) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono31 : ∀ a i', CodeReq.singleton (hphBase + 124) (.JALR .x0 .x1 (0 : BitVec 12)) a = some i'
      → hphCode a = some i' :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 31
      (hphBase + 124) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have ha_t : hphBase + 88 + signExtend13 (32 : BitVec 13) = hphBase + 120 := hphAddr_beq_taken
  have ha_f : (hphBase + 88 : Word) + 4 = hphBase + 92 := hphAddr_beq_fall
  have ha_back : (hphBase + 116) + signExtend21 (-32 : BitVec 21) = hphBase + 84 := hphAddr_jal_back
  induction m generalizing i v6 v7 v28 with
  | zero =>
    have hi32 : i = 32 := by omega
    subst hi32
    have hLi := li_spec_gen_within .x6 v6 (32 : Word) (hphBase + 84) (by decide)
    have hLi_fr := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x5 ↦ᵣ BitVec.ofNat 64 32) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip 32) **
       bytesRegion thisPtr thisBytes) (by pcFree)
      (cpsTripleWithin_extend_code hmono21 hLi)
    have hbeq := beq_spec_gen_within .x5 .x6 (32 : BitVec 13)
      (BitVec.ofNat 64 32) (32 : Word) (hphBase + 88)
    rw [ha_t, ha_f] at hbeq
    have hTaken0 := cpsBranchWithin_takenStripPure2 hbeq (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact h_pure.2 (by decide))
    have hTaken_fr := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip 32) **
       bytesRegion thisPtr thisBytes) (by pcFree) hTaken0
    have hTaken_ext := cpsTripleWithin_extend_code hmono22 hTaken_fr
    have hSeq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
      hLi_fr hTaken_ext
    have hLi2 := li_spec_gen_within .x10 (thisPtr + BitVec.ofNat 64 skip) (0 : Word)
      (hphBase + 120) (by decide)
    have hLi2_fr := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ retHdr) ** (.x5 ↦ᵣ BitVec.ofNat 64 32) ** (.x6 ↦ᵣ (32 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip 32) **
       bytesRegion thisPtr thisBytes) (by pcFree)
      (cpsTripleWithin_extend_code hmono30 hLi2)
    have hRet0 := EvmAsm.Evm64.ret_spec_within' (hphBase + 124) retHdr
    rw [hret] at hRet0
    have hRet_fr := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ BitVec.ofNat 64 32) ** (.x6 ↦ᵣ (32 : Word)) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) ** (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip 32) **
       bytesRegion thisPtr thisBytes) (by pcFree)
      (cpsTripleWithin_extend_code hmono31 hRet0)
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hSeq hLi2_fr
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hRet_fr
    exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 + 1 ≤ 9 * 0 + 4 from by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => by
          rw [hphWindow_full thisBytes claimedBytes skip hclaimed] at hq
          exact sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x5) (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
            (sepConj_mono (fun _ x => x) (sepConj_mono (regIs_implies_regOwn .x12)
            (fun _ x => x)))))))) h hq) s2)
  | succ k ih =>
    have hi32 : i < 32 := by omega
    have hLi := li_spec_gen_within .x6 v6 (32 : Word) (hphBase + 84) (by decide)
    have hLi_fr := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x5 ↦ᵣ BitVec.ofNat 64 i) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip i) **
       bytesRegion thisPtr thisBytes) (by pcFree)
      (cpsTripleWithin_extend_code hmono21 hLi)
    have hbeq := beq_spec_gen_within .x5 .x6 (32 : BitVec 13)
      (BitVec.ofNat 64 i) (32 : Word) (hphBase + 88)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 i ≠ (32 : Word) := hphOfNat_ne_32 i hi32
    have hNt0 := cpsBranchWithin_ntakenStripPure2 hbeq (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
      exact hne h_pure.2)
    have hNt_fr := cpsTripleWithin_frameR
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
       (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
       (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
       bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip i) **
       bytesRegion thisPtr thisBytes) (by pcFree) hNt0
    have hNt_ext := cpsTripleWithin_extend_code hmono22 hNt_fr
    have hSeq := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp)
      hLi_fr hNt_ext
    have hsi : skip + 1 + i < thisBytes.length := by omega
    have body := hph_copy_body_spec_within retHdr thisPtr w11 v7 v28
      thisBytes claimedBytes skip i hsalign hsi (by omega) (hsvalid _ hsi) hclaimed hi32
    have hjal := jal_x0_spec_gen_within (-32 : BitVec 21) (hphBase + 116)
    rw [ha_back] at hjal
    have hjal_S := cpsTripleWithin_weaken
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (fun h hp => by simpa only [sepConj_emp_left'] using hp)
      (cpsTripleWithin_frameR
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) **
         (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) **
         (.x5 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x6 ↦ᵣ (32 : Word)) **
         (.x7 ↦ᵣ (hphClaimed + BitVec.ofNat 64 i)) **
         (.x28 ↦ᵣ (thisBytes[skip + 1 + i]'hsi).zeroExtend 64) **
         bytesRegion hphClaimed (hphWindow thisBytes claimedBytes skip (i + 1)) **
         bytesRegion thisPtr thisBytes) (by pcFree)
        (cpsTripleWithin_extend_code hmono29 hjal))
    have ihspec := ih (32 : Word) (hphClaimed + BitVec.ofNat 64 i)
      ((thisBytes[skip + 1 + i]'hsi).zeroExtend 64) (i + 1) (by omega) (by omega)
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) hSeq body
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    rw [show 9 * (k + 1) + 4 = (1 + 1) + 6 + 1 + (9 * k + 4) from by omega]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) s1234

/-- Status/outcome simplifiers keyed on the ok-predicate. -/
theorem hphStatus_false {thisBytes : List (BitVec 8)}
    (hok : headersParentHash_ok thisBytes = false) :
    headersParentHash_status thisBytes = 1 := by
  simp only [headersParentHash_status, hok]
  exact if_neg (by decide)

private theorem hphStatus_true {thisBytes : List (BitVec 8)}
    (hok : headersParentHash_ok thisBytes = true) :
    headersParentHash_status thisBytes = 0 := by
  simp only [headersParentHash_status, hok]
  exact if_pos (by decide)

theorem hphOut_false {thisBytes claimedBytes : List (BitVec 8)}
    (hok : headersParentHash_ok thisBytes = false) :
    headersParentHash_out thisBytes claimedBytes = claimedBytes := by
  simp only [headersParentHash_out, hok]
  exact if_neg (by decide)

private theorem hphOut_true {thisBytes claimedBytes : List (BitVec 8)}
    (hok : headersParentHash_ok thisBytes = true) :
    headersParentHash_out thisBytes claimedBytes =
      (thisBytes.drop (headersParentHash_skip (headersParentHash_b0 thisBytes) + 1)).take 32 := by
  simp only [headersParentHash_out, hok]
  exact if_pos (by decide)

/-- Hoisted address arithmetic for the BLTU at instruction 16 (PC +64, taken → +128). -/
private theorem hphSE16 : signExtend13 (brOff (GuestAddrs.headers_parent_hash + 128)
    (GuestAddrs.headers_parent_hash + 64)) = (64 : Word) := by decide

private theorem hphA16t : hphBase + 64 + (64 : Word) = hphBase + 128 := by bv_omega

private theorem hphA16f : hphBase + 64 + 4 = hphBase + 68 := by bv_omega

/-- Hoisted address arithmetic for the BNE at instruction 19 (PC +76, taken → +128). -/
private theorem hphSE19 : signExtend13 (52 : BitVec 13) = (52 : Word) := by decide

private theorem hphA19t : hphBase + 76 + (52 : Word) = hphBase + 128 := by bv_omega

private theorem hphA19f : hphBase + 76 + 4 = hphBase + 80 := by bv_omega

/-- The tail from instruction 15 (PC `hphBase + 60`): remaining-length check, the
`0xa0` byte check, and the 32-byte copy loop.  Produces the final outcome
(status 0 + copied parent hash, or status 1 + unchanged output). -/
theorem hph_from15_spec_within (retHdr : Word) (hret : retHdr &&& ~~~(1 : Word) = retHdr)
    (thisPtr w11 : Word) (skip : Nat) (v5 v6 v7 v28 : Word)
    (thisBytes claimedBytes : List (BitVec 8))
    (hsalign : thisPtr.toNat % 8 = 0)
    (hsover : thisPtr.toNat + thisBytes.length ≤ 2 ^ 64)
    (hsvalid : ∀ k, k < thisBytes.length → isValidByteAccess (thisPtr + BitVec.ofNat 64 k) = true)
    (hclaimed : claimedBytes.length = 32)
    (hlo : 192 ≤ headersParentHash_b0 thisBytes)
    (hhi : headersParentHash_b0 thisBytes ≤ 249)
    (hskip : skip = headersParentHash_skip (headersParentHash_b0 thisBytes))
    (hw11 : w11.toNat = thisBytes.length - skip)
    (hskiplen : skip ≤ thisBytes.length) :
    cpsTripleWithin 298 (hphBase + 60) retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (headersParentHash_status thisBytes)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        bytesRegion hphClaimed (headersParentHash_out thisBytes claimedBytes) **
        bytesRegion thisPtr thisBytes ** regOwn .x11 ** regOwn .x12) := by
  have hmono15 : ∀ a i, CodeReq.singleton (hphBase + 60) (.LI .x5 (33 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 15
      (hphBase + 4 * 15) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono16 : ∀ a i, CodeReq.singleton (hphBase + 64)
      (.BLTU .x11 .x5 (brOff (GuestAddrs.headers_parent_hash + 128)
        (GuestAddrs.headers_parent_hash + 64))) a = some i → hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 16
      (hphBase + 4 * 16) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono17 : ∀ a i, CodeReq.singleton (hphBase + 68) (.LBU .x6 .x10 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 17
      (hphBase + 4 * 17) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono18 : ∀ a i, CodeReq.singleton (hphBase + 72) (.LI .x7 (160 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 18
      (hphBase + 4 * 18) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono19 : ∀ a i, CodeReq.singleton (hphBase + 76) (.BNE .x6 .x7 (52 : BitVec 13)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 19
      (hphBase + 4 * 19) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono20 : ∀ a i, CodeReq.singleton (hphBase + 80) (.LI .x5 (0 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 20
      (hphBase + 4 * 20) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono32 : ∀ a i, CodeReq.singleton (hphBase + 128) (.LI .x10 (1 : Word)) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 32
      (hphBase + 4 * 32) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  have hmono33 : ∀ a i, CodeReq.singleton (hphBase + 132) (.JALR .x0 .x1 0) a = some i →
      hphCode a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr hphBase headersParentHash_prog 33
      (hphBase + 4 * 33) (by rw [headersParentHash_length]; norm_num)
      (by rw [headersParentHash_length]; norm_num) (by bv_omega))
  -- instruction 15: LI x5, 33
  have h33 : cpsTripleWithin 1 (hphBase + 60) (hphBase + 64) hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
        (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h0 := cpsTripleWithin_extend_code hmono15
      (li_spec_gen_within .x5 v5 (33 : Word) (hphBase + 60) (by decide))
    have h0f := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
        (.x12 ↦ᵣ hphClaimed)) ** ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp) h0f
  -- instruction 16: BLTU x11, x5 (is w11 < 33?)
  have hBr0 := bltu_spec_gen_within .x11 .x5
    (brOff (GuestAddrs.headers_parent_hash + 128) (GuestAddrs.headers_parent_hash + 64))
    w11 (33 : Word) (hphBase + 64)
  rw [hphSE16, hphA16t, hphA16f] at hBr0
  -- the fail epilogue (instructions 32, 33), from the BLTU's taken target
  have hFail : cpsTripleWithin 2 (hphBase + 128) retHdr hphCode
      ((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
        (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
      ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
        (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
        bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
    have h1 : cpsTripleWithin 1 (hphBase + 128) (hphBase + 132) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) **
          (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
      have h0 := cpsTripleWithin_extend_code hmono32
        (li_spec_gen_within .x10 (thisPtr + BitVec.ofNat 64 skip) (1 : Word) (hphBase + 128)
          (by decide))
      have h0f := cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word))) ** ((.x12 ↦ᵣ hphClaimed) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hp => by xperm_hyp hp) h0f
    have hRet0 := cpsTripleWithin_extend_code hmono33
      (EvmAsm.Evm64.ret_spec_within' (hphBase + 132) retHdr)
    rw [hret] at hRet0
    have hRet : cpsTripleWithin 1 (hphBase + 132) retHdr hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
      cpsTripleWithin_frameR
        (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) ** (.x12 ↦ᵣ hphClaimed) **
          (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hRet0
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1 hRet
    exact cpsTripleWithin_mono_nSteps (show 1 + 1 ≤ 2 from by omega) s1
  by_cases hlenlt : w11.toNat < 33
  · -- Outcome: remaining length too short (len - skip < 33) → status 1.
    have hult : BitVec.ult w11 (33 : Word) := by
      simp only [BitVec.ult, decide_eq_true_eq, show (33 : Word).toNat = 33 from by decide]
      exact hlenlt
    have hTaken0 := cpsBranchWithin_takenStripPure2 hBr0 (fun hp hQf => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
      exact h_pure.2 hult)
    have hTaken_fr := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x12 ↦ᵣ hphClaimed) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
        (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hTaken0
    have hTaken : cpsTripleWithin 1 (hphBase + 64) (hphBase + 128) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ v6) **
          (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
      cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
        (cpsTripleWithin_extend_code hmono16 hTaken_fr)
    have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h33 hTaken
    have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hFail
    have hnot : ¬ (headersParentHash_skip (headersParentHash_b0 thisBytes) + 33 ≤
        thisBytes.length) := by omega
    have hok : headersParentHash_ok thisBytes = false := by
      simp only [headersParentHash_ok, decide_eq_false hnot, Bool.and_false, Bool.false_and]
    exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 2 ≤ 298 from by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
        rw [hphStatus_false hok, hphOut_false hok]
        have hq' := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
          (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x5)
          (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono (regIs_implies_regOwn .x6)
          (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
          (sepConj_mono (fun _ x => x) (fun _ x => x))))))))) h hq
        xperm_hyp hq') s2)
  · push Not at hlenlt
    have hsk : skip < thisBytes.length := by omega
    have hnotult : ¬ BitVec.ult w11 (33 : Word) := by
      simp only [BitVec.ult, decide_eq_true_eq, show (33 : Word).toNat = 33 from by decide]
      omega
    -- fallthrough of instruction 16
    have hNt0 := cpsBranchWithin_ntakenStripPure2 hBr0 (fun hp hQt => by
      obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
      exact hnotult h_pure.2)
    have hNt_fr := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x12 ↦ᵣ hphClaimed) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) **
        (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt0
    have hNt : cpsTripleWithin 1 (hphBase + 64) (hphBase + 68) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
      cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
        (cpsTripleWithin_extend_code hmono16 hNt_fr)
    -- instruction 17: LBU x6 ← thisBytes[skip]
    have hLbu0 := bytesRegion_lbu_within .x6 .x10 thisPtr v6 (hphBase + 68) thisBytes skip
      (by decide) hsalign hsk (by omega) (hsvalid skip hsk)
    have hLbu_fr := cpsTripleWithin_frameR
      (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ w11) ** (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
        (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28)) ** bytesRegion hphClaimed claimedBytes) (by pcFree) hLbu0
    have hLbu : cpsTripleWithin 1 (hphBase + 68) (hphBase + 72) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
          (.x28 ↦ᵣ v28) ** bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
      cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
        (cpsTripleWithin_extend_code hmono17 hLbu_fr)
    -- instruction 18: LI x7, 160
    have h160 : cpsTripleWithin 1 (hphBase + 72) (hphBase + 76) hphCode
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ v7) ** (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
        ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
          (.x28 ↦ᵣ v28) **
          bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
      have h0 := cpsTripleWithin_extend_code hmono18
        (li_spec_gen_within .x7 v7 (160 : Word) (hphBase + 72) (by decide))
      have h0f := cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
          (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x28 ↦ᵣ v28)) **
          (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0
      exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hp => by xperm_hyp hp) h0f
    -- instruction 19: BNE x6, x7
    have hBr190 := bne_spec_gen_within .x6 .x7 (52 : BitVec 13)
      ((thisBytes[skip]'hsk).zeroExtend 64) (160 : Word) (hphBase + 76)
    rw [hphSE19, hphA19t, hphA19f] at hBr190
    by_cases hbyte : thisBytes[skip]'hsk = 0xa0
    · -- Outcome: success — the byte is 0xa0, run the copy loop.
      have hNt19 := cpsBranchWithin_ntakenStripPure2 hBr190 (fun hp hQt => by
        obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQt
        exact h_pure.2 ((hphByte160_eq _).2 hbyte))
      have hNt19_fr := cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x28 ↦ᵣ v28)) **
          (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) hNt19
      have hNt19e : cpsTripleWithin 1 (hphBase + 76) (hphBase + 80) hphCode
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
        cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
          (cpsTripleWithin_extend_code hmono19 hNt19_fr)
      -- instruction 20: LI x5, 0
      have hLi0 : cpsTripleWithin 1 (hphBase + 80) (hphBase + 84) hphCode
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (0 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
        have h0 := cpsTripleWithin_extend_code hmono20
          (li_spec_gen_within .x5 (33 : Word) (0 : Word) (hphBase + 80) (by decide))
        have h0f := cpsTripleWithin_frameR
          (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed)) ** ((.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) **
            (.x7 ↦ᵣ (160 : Word)) ** (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0
        exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
          (fun h hp => by xperm_hyp hp) h0f
      -- the copy loop: 32 iterations from i = 0
      have hLoop := hph_loop_spec_within retHdr hret thisPtr w11 skip
        ((thisBytes[skip]'hsk).zeroExtend 64) (160 : Word) v28
        thisBytes claimedBytes hsalign hsover hsvalid hclaimed 32 0 (by omega) (by omega)
      rw [hphWindow_zero thisBytes claimedBytes skip,
        show (BitVec.ofNat 64 0 : Word) = 0 from by decide] at hLoop
      -- chain the six prefix instructions with the loop
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h33 hNt
      have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hLbu
      have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 h160
      have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hNt19e
      have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hLi0
      have s6 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s5 hLoop
      have hlenge : headersParentHash_skip (headersParentHash_b0 thisBytes) + 33 ≤
          thisBytes.length := by omega
      have hbytet : (thisBytes[headersParentHash_skip (headersParentHash_b0 thisBytes)]?.getD
            0 == 0xa0) = true := by
        rw [beq_iff_eq, ← hskip, List.getElem?_eq_getElem hsk, Option.getD_some]
        exact hbyte
      have hok : headersParentHash_ok thisBytes = true := by
        simp only [headersParentHash_ok, decide_eq_true hlo, decide_eq_true hhi,
          decide_eq_true hlenge, hbytet, Bool.and_true]
      exact cpsTripleWithin_mono_nSteps
        (show 1 + 1 + 1 + 1 + 1 + 1 + (9 * 32 + 4) ≤ 298 from by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
          rw [hphStatus_true hok, hphOut_true hok, ← hskip]
          have hq' := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x11)
            (sepConj_mono (fun _ x => x)
            (sepConj_mono (fun _ x => x) (fun _ x => x))))))))) h hq
          xperm_hyp hq') s6)
    · -- Outcome: byte mismatch (≠ 0xa0) → status 1.
      have hNez : (thisBytes[skip]'hsk).zeroExtend 64 ≠ (160 : Word) :=
        fun h => hbyte ((hphByte160_eq _).1 h)
      have hTaken19 := cpsBranchWithin_takenStripPure2 hBr190 (fun hp hQf => by
        obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, h_pure⟩⟩ := hQf
        exact hNez h_pure.2)
      have hTaken19_fr := cpsTripleWithin_frameR
        (((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
          (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) ** (.x28 ↦ᵣ v28)) **
          (bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree)
        hTaken19
      have hTaken19e : cpsTripleWithin 1 (hphBase + 76) (hphBase + 128) hphCode
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
        cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp)
          (cpsTripleWithin_extend_code hmono19 hTaken19_fr)
      -- the fail epilogue, entered with x6 = byte, x7 = 160
      have hFail' : cpsTripleWithin 2 (hphBase + 128) retHdr hphCode
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
            (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
            (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
          ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
            (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) **
            (.x7 ↦ᵣ (160 : Word)) ** (.x28 ↦ᵣ v28) **
            bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
        have h1 : cpsTripleWithin 1 (hphBase + 128) (hphBase + 132) hphCode
            ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (thisPtr + BitVec.ofNat 64 skip)) ** (.x11 ↦ᵣ w11) **
              (.x12 ↦ᵣ hphClaimed) ** (.x5 ↦ᵣ (33 : Word)) **
              (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
              (.x28 ↦ᵣ v28) **
              bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
            ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
              (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) **
              (.x7 ↦ᵣ (160 : Word)) ** (.x28 ↦ᵣ v28) **
              bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) := by
          have h0 := cpsTripleWithin_extend_code hmono32
            (li_spec_gen_within .x10 (thisPtr + BitVec.ofNat 64 skip) (1 : Word) (hphBase + 128)
              (by decide))
          have h0f := cpsTripleWithin_frameR
            (((.x1 ↦ᵣ retHdr) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word))) ** ((.x12 ↦ᵣ hphClaimed) **
              (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) ** (.x7 ↦ᵣ (160 : Word)) **
              (.x28 ↦ᵣ v28) **
              bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree) h0
          exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
            (fun h hp => by xperm_hyp hp) h0f
        have hRet0 := cpsTripleWithin_extend_code hmono33
          (EvmAsm.Evm64.ret_spec_within' (hphBase + 132) retHdr)
        rw [hret] at hRet0
        have hRet : cpsTripleWithin 1 (hphBase + 132) retHdr hphCode
            ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
              (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) **
              (.x7 ↦ᵣ (160 : Word)) ** (.x28 ↦ᵣ v28) **
              bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)
            ((.x1 ↦ᵣ retHdr) ** (.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
              (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) **
              (.x7 ↦ᵣ (160 : Word)) ** (.x28 ↦ᵣ v28) **
              bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes) :=
          cpsTripleWithin_frameR
            (((.x10 ↦ᵣ (1 : Word)) ** (.x11 ↦ᵣ w11) ** (.x5 ↦ᵣ (33 : Word)) **
              (.x12 ↦ᵣ hphClaimed) ** (.x6 ↦ᵣ (thisBytes[skip]'hsk).zeroExtend 64) **
              (.x7 ↦ᵣ (160 : Word)) ** (.x28 ↦ᵣ v28) **
              bytesRegion hphClaimed claimedBytes ** bytesRegion thisPtr thisBytes)) (by pcFree)
            hRet0
        have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h1 hRet
        exact cpsTripleWithin_mono_nSteps (show 1 + 1 ≤ 2 from by omega) s1
      have s1 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) h33 hNt
      have s2 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s1 hLbu
      have s3 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s2 h160
      have s4 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s3 hTaken19e
      have s5 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s4 hFail'
      have hbeqf : (thisBytes[headersParentHash_skip (headersParentHash_b0 thisBytes)]?.getD
            0 == 0xa0) = false := by
        rw [← hskip, List.getElem?_eq_getElem hsk, Option.getD_some]
        exact beq_eq_false_iff_ne.mpr hbyte
      have hok : headersParentHash_ok thisBytes = false := by
        simp only [headersParentHash_ok, hbeqf, Bool.and_false]
      exact cpsTripleWithin_mono_nSteps (show 1 + 1 + 1 + 1 + 1 + 2 ≤ 298 from by omega)
        (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => by
          rw [hphStatus_false hok, hphOut_false hok]
          have hq' := sepConj_mono (fun _ x => x) (sepConj_mono (fun _ x => x)
            (sepConj_mono (regIs_implies_regOwn .x11) (sepConj_mono (regIs_implies_regOwn .x5)
            (sepConj_mono (regIs_implies_regOwn .x12) (sepConj_mono (regIs_implies_regOwn .x6)
            (sepConj_mono (regIs_implies_regOwn .x7) (sepConj_mono (regIs_implies_regOwn .x28)
            (sepConj_mono (fun _ x => x) (fun _ x => x))))))))) h hq
          xperm_hyp hq') s5)

end EvmAsm.Codegen
