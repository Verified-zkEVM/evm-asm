/-
  EvmAsm.Rv64.SAsm.ParentHeaderMemcmp

  A REAL byte-equality (`memcmp`) countdown loop over two read-only byte
  regions, discharged with a genuine accumulator invariant via the
  register-agnostic `countdownLoop_spec` bridge (bead evm-asm-4ch8f follow-up
  `evm-asm-ffziu`).

  This is the load-bearing core of the re-emitted, verified drop-in for the
  `parent_header_matches_witness_first` guest routine
  (`EvmAsm/Codegen/Programs/BlockHashPredicates.lean`).  That routine, after an
  SSZ offset-table decode, compares `parent_header_rlp[0..len)` against
  `witness.headers[0]` byte-for-byte.  The original guest loop early-exits on
  the first mismatch; the verified re-emission instead accumulates a
  branch-free match flag over ALL `len` bytes — a functionally identical
  drop-in (both compute `is_match = 1 ⇔ the two spans agree`), reshaped into the
  exact bottom-decrement countdown `countdownLoop_spec` recognizes:

  ```
    hdr:  beq   ctr, x0, exit        -- header guard
          lbu   b1, 0(p1)            -- b1 := parent[i]
          lbu   b2, 0(p2)            -- b2 := section[off0 + i]
          xor   b1, b1, b2           -- b1 := b1 ^ b2  (0 iff equal)
          sltiu eq, b1, 1            -- eq := (b1 == 0) ? 1 : 0
          and   mf, mf, eq           -- matchFlag &= eq
          addi  p1, p1, 1
          addi  p2, p2, 1
          addi  ctr, ctr, -1
          jal   x0, hdr              -- back-edge
    exit:
  ```

  The invariant carried through `countdownLoop_spec` at remaining count `n` is
  the genuine running match flag `matchFlag = memcmpFlag pb sb off0 (len - n)`
  (the bitwise-AND fold of the per-byte equalities over the first `len - n`
  byte pairs) — NOT vacuous, NOT `decide`-away.  Both byte regions are read
  only, so they are simply framed (unchanged) through every iteration.

  Strictly additive: builds only on `cpsTripleWithin`, `countdownLoop_spec`,
  and `bytesRegion_lbu_within`; touches no `Ast`/`Vc`/`StmtSound*`/`blockOk`.
-/

import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64
namespace SAsm
namespace ParentHeaderMemcmp

open EvmAsm.Rv64.Tactics

-- ============================================================================
-- The running match flag: a bitwise-AND fold of per-byte equalities.
-- ============================================================================

/-- The word `1` if the two bytes agree, else `0`. -/
def eqByteWord (x y : BitVec 8) : Word := if x = y then (1 : Word) else (0 : Word)

/-- `memcmpFlag pb sb off0 p` is `1` iff the first `p` byte pairs
    `(pb[k], sb[off0+k])` all agree, computed as the bitwise-AND fold of the
    per-byte equality words — exactly the sequence of `and mf, mf, eq`
    accumulations the loop performs.  `0` otherwise. -/
def memcmpFlag (pb sb : List (BitVec 8)) (off0 : Nat) : Nat → Word
  | 0     => (1 : Word)
  | p + 1 => memcmpFlag pb sb off0 p &&& eqByteWord (pb.getD p 0) (sb.getD (off0 + p) 0)

@[simp] theorem memcmpFlag_zero (pb sb : List (BitVec 8)) (off0 : Nat) :
    memcmpFlag pb sb off0 0 = (1 : Word) := rfl

theorem memcmpFlag_succ (pb sb : List (BitVec 8)) (off0 p : Nat) :
    memcmpFlag pb sb off0 (p + 1)
      = memcmpFlag pb sb off0 p &&& eqByteWord (pb.getD p 0) (sb.getD (off0 + p) 0) := rfl

-- ============================================================================
-- Byte-level equality arithmetic (the xor ; sltiu combo).
-- ============================================================================

/-- Zero-extension `BitVec 8 → BitVec 64` is injective. -/
private theorem zeroExtend8_inj {x y : BitVec 8}
    (h : (x.zeroExtend 64) = (y.zeroExtend 64)) : x = y := by
  have hx := congrArg (BitVec.truncate 8) h
  simpa using hx

/-- `xor` of two zero-extended bytes is zero iff the bytes agree. -/
private theorem xor_zext_eq_zero_iff (x y : BitVec 8) :
    ((x.zeroExtend 64) ^^^ (y.zeroExtend 64)) = (0 : Word) ↔ x = y := by
  constructor
  · intro h
    have : (x.zeroExtend 64) = (y.zeroExtend 64) := by
      have := BitVec.xor_eq_zero_iff.mp h
      exact this
    exact zeroExtend8_inj this
  · intro h; subst h; simp

/-- `sltiu v, 1` computes `(v == 0) ? 1 : 0`. -/
private theorem ult_one_iff_zero (v : Word) :
    (if BitVec.ult v (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word))
      = (if v = 0 then (1 : Word) else (0 : Word)) := by
  have hse : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have h1 : (1 : Word).toNat = 1 := by decide
  have hult2 : BitVec.ult v (1 : Word) = decide (v = 0) := by
    rw [BitVec.ult, h1]
    by_cases hv : v = 0
    · subst hv; simp
    · have hp : 0 < v.toNat := by
        rcases Nat.eq_zero_or_pos v.toNat with h0 | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hv
        · exact h
      rw [decide_eq_false hv]
      exact decide_eq_false (by omega)
  rw [hse, hult2]
  by_cases hv : v = 0 <;> simp [hv]

/-- The `xor ; sltiu` byte-equality: for two bytes, the combo produces
    `eqByteWord`. -/
theorem eq_combo (x y : BitVec 8) :
    (if BitVec.ult ((x.zeroExtend 64) ^^^ (y.zeroExtend 64)) (signExtend12 (1 : BitVec 12))
      then (1 : Word) else (0 : Word))
      = eqByteWord x y := by
  rw [ult_one_iff_zero]
  unfold eqByteWord
  by_cases h : x = y
  · subst h
    rw [if_pos (by rw [xor_zext_eq_zero_iff]), if_pos rfl]
  · have hne : ¬ (((x.zeroExtend 64) ^^^ (y.zeroExtend 64)) = (0 : Word)) := by
      rw [xor_zext_eq_zero_iff]; exact h
    rw [if_neg hne, if_neg h]

-- ============================================================================
-- The concrete memcmp loop program (10 instructions) at a symbolic header.
-- ============================================================================

/-- The bottom-decrement memcmp loop, spelled out.  Registers:
    `ctr = x28`, `mf = x5`, `p1 = x6`, `p2 = x7`, scratch `b1 = x29`,
    `b2 = x30`, `eq = x31`. -/
def loopProgList : List Instr :=
  [ .BEQ .x28 .x0 (40 : BitVec 13),   -- 0: guard, exit at hdr+40
    .LBU .x29 .x6 (0 : BitVec 12),    -- 1: b1 := parent[p1]
    .LBU .x30 .x7 (0 : BitVec 12),    -- 2: b2 := section[p2]
    .XOR .x29 .x29 .x30,              -- 3: b1 := b1 ^ b2
    .SLTIU .x31 .x29 (1 : BitVec 12), -- 4: eq := (b1 == 0) ? 1 : 0
    .AND .x5 .x5 .x31,                -- 5: mf := mf & eq
    .ADDI .x6 .x6 (1 : BitVec 12),    -- 6: p1++
    .ADDI .x7 .x7 (1 : BitVec 12),    -- 7: p2++
    .ADDI .x28 .x28 (-1 : BitVec 12), -- 8: ctr--
    .JAL .x0 (-36 : BitVec 21) ]      -- 9: back-edge to hdr

/-- The loop `CodeReq`, anchored at `0x1000`. -/
def loopCr : CodeReq := CodeReq.ofProg 0x1000 loopProgList

/-- Code-membership: instruction `idx` of the loop sits in `loopCr`. -/
private theorem memAt (idx : Nat) (addr : Word) (instr : Instr)
    (hk : idx < loopProgList.length) (hbound : 4 * loopProgList.length < 2 ^ 64)
    (haddr : addr = (0x1000 : Word) + BitVec.ofNat 64 (4 * idx))
    (hget : loopProgList.get ⟨idx, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i → loopCr a = some i := by
  have m := CodeReq.ofProg_lookup_addr (0x1000 : Word) loopProgList idx addr hk hbound haddr
  rw [hget] at m
  exact CodeReq.singleton_mono m

-- ============================================================================
-- The loop invariant: running match flag + two cursors + framed regions.
-- ============================================================================

/-- Loop invariant at remaining count `n` (`p := len - n` bytes processed):
    `mf = memcmpFlag pb sb off0 (len - n)`, the two read cursors advanced to
    `len - n`, the three scratch registers owned (arbitrary), and both byte
    regions framed unchanged. -/
def memcmpInv (parentBase secBase : Word) (pb sb : List (BitVec 8))
    (off0 len : Nat) (n : Nat) : Assertion :=
  (.x5 ↦ᵣ memcmpFlag pb sb off0 (len - n))
    ** (.x6 ↦ᵣ (parentBase + BitVec.ofNat 64 (len - n)))
    ** (.x7 ↦ᵣ (secBase + BitVec.ofNat 64 (off0 + (len - n))))
    ** regOwn .x29 ** regOwn .x30 ** regOwn .x31
    ** bytesRegion parentBase pb ** bytesRegion secBase sb

theorem pcFree_memcmpInv (parentBase secBase : Word) (pb sb : List (BitVec 8))
    (off0 len n : Nat) : (memcmpInv parentBase secBase pb sb off0 len n).pcFree := by
  unfold memcmpInv
  exact pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
    (pcFree_sepConj pcFree_regOwn (pcFree_sepConj pcFree_regOwn (pcFree_sepConj pcFree_regOwn
      (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)))))))

-- ============================================================================
-- Small address / counter helpers.
-- ============================================================================

private theorem ofNat_add' (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem ofNat_succ_addr (b : Word) (p : Nat) :
    (b + BitVec.ofNat 64 p) + signExtend12 (1 : BitVec 12) = b + BitVec.ofNat 64 (p + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = BitVec.ofNat 64 1 from by decide,
      BitVec.add_assoc, ofNat_add']

private theorem cnt_step_down (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1 := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_add']
  rw [e1, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
      BitVec.add_assoc, show (1 : Word) + (-1 : Word) = 0 from by decide]
  exact BitVec.add_zero _

-- ============================================================================
-- The per-iteration loop body triple.
-- ============================================================================

/-- **The per-iteration memcmp loop body** (`0x1004 → 0x1000`): read one byte
    from each region, fold the equality into the match flag, advance both
    cursors, decrement the counter, back-edge to the header.  Discharges the
    `hbody` obligation of `countdownLoop_spec` with the genuine
    `memcmpFlag`-fold invariant. -/
theorem memcmpLoopBody_spec
    (parentBase secBase : Word) (pb sb : List (BitVec 8)) (off0 len n : Nat)
    (hn : n < len)
    (hpblen : pb.length = len)
    (hsblen : off0 + len ≤ sb.length)
    (hpalign : parentBase.toNat % 8 = 0) (hsalign : secBase.toNat % 8 = 0)
    (hpover : parentBase.toNat + len < 2 ^ 64)
    (hsover : secBase.toNat + (off0 + len) < 2 ^ 64)
    (hpvalid : ∀ i, i < len → isValidByteAccess (parentBase + BitVec.ofNat 64 i) = true)
    (hsvalid : ∀ i, i < len →
      isValidByteAccess (secBase + BitVec.ofNat 64 (off0 + i)) = true) :
    cpsTripleWithin 9 (0x1004 : Word) (0x1000 : Word) loopCr
      ((.x28 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** memcmpInv parentBase secBase pb sb off0 len (n + 1))
      ((.x28 ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** memcmpInv parentBase secBase pb sb off0 len n) := by
  -- `p` = number of bytes already processed on entry (= index read this pass).
  set p := len - (n + 1) with hp
  have hpn : len - n = p + 1 := by omega
  have hplt : p < len := by omega
  have hphi : p < pb.length := by omega
  have hshi : off0 + p < sb.length := by omega
  simp only [memcmpInv, hpn, loopCr, loopProgList, CodeReq.ofProg_cons, CodeReq.ofProg_nil,
    CodeReq.union_empty_right]
  -- Peel the three scratch registers to concrete values.
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x29)
      (P := (.x28 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (.x5 ↦ᵣ memcmpFlag pb sb off0 p) ** (.x6 ↦ᵣ (parentBase + BitVec.ofNat 64 p))
        ** (.x7 ↦ᵣ (secBase + BitVec.ofNat 64 (off0 + p)))
        ** bytesRegion parentBase pb ** bytesRegion secBase sb
        ** regOwn .x30 ** regOwn .x31)
      (fun v29 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x30)
      (P := (.x28 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (.x5 ↦ᵣ memcmpFlag pb sb off0 p) ** (.x6 ↦ᵣ (parentBase + BitVec.ofNat 64 p))
        ** (.x7 ↦ᵣ (secBase + BitVec.ofNat 64 (off0 + p)))
        ** bytesRegion parentBase pb ** bytesRegion secBase sb
        ** (.x29 ↦ᵣ v29) ** regOwn .x31)
      (fun v30 => ?_))
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ h => h)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x31)
      (P := (.x28 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** (.x5 ↦ᵣ memcmpFlag pb sb off0 p) ** (.x6 ↦ᵣ (parentBase + BitVec.ofNat 64 p))
        ** (.x7 ↦ᵣ (secBase + BitVec.ofNat 64 (off0 + p)))
        ** bytesRegion parentBase pb ** bytesRegion secBase sb
        ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30))
      (fun v31 => ?_))
  -- The concrete straight-line block.
  have hlbu1 := bytesRegion_lbu_within .x29 .x6 parentBase v29 (0x1004 : Word) pb p
    (by decide) hpalign hphi (by omega) (hpvalid p hplt)
  have hlbu2 := bytesRegion_lbu_within .x30 .x7 secBase v30 (0x1008 : Word) sb (off0 + p)
    (by decide) hsalign hshi (by omega) (hsvalid p hplt)
  have hxor := xor_spec_gen_rd_eq_rs1_within .x29 .x30
    ((pb[p]'hphi).zeroExtend 64) ((sb[off0 + p]'hshi).zeroExtend 64) (0x100C : Word) (by decide)
  have hsltiu := sltiu_spec_gen_within .x31 .x29 v31
    (((pb[p]'hphi).zeroExtend 64) ^^^ ((sb[off0 + p]'hshi).zeroExtend 64)) (1 : BitVec 12)
    (0x1010 : Word) (by decide)
  have hand := and_spec_gen_rd_eq_rs1_within .x5 .x31
    (memcmpFlag pb sb off0 p)
    (if BitVec.ult (((pb[p]'hphi).zeroExtend 64) ^^^ ((sb[off0 + p]'hshi).zeroExtend 64))
      (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word))
    (0x1014 : Word) (by decide)
  have haddi1 := addi_spec_gen_same_within .x6 (parentBase + BitVec.ofNat 64 p) (1 : BitVec 12)
    (0x1018 : Word) (by decide)
  rw [ofNat_succ_addr] at haddi1
  have haddi2 := addi_spec_gen_same_within .x7 (secBase + BitVec.ofNat 64 (off0 + p))
    (1 : BitVec 12) (0x101C : Word) (by decide)
  rw [ofNat_succ_addr, show off0 + p + 1 = off0 + (p + 1) from Nat.add_assoc off0 p 1] at haddi2
  have haddi3 := addi_spec_gen_same_within .x28 (BitVec.ofNat 64 (n + 1)) (-1 : BitVec 12)
    (0x1020 : Word) (by decide)
  rw [cnt_step_down] at haddi3
  have hjal := jal_x0_spec_gen_within (-36 : BitVec 21) (0x1024 : Word)
  rw [show (0x1024 : Word) + signExtend21 (-36 : BitVec 21) = (0x1000 : Word) from by decide]
    at hjal
  -- Reshape the goal's match-flag fold so the block's output matches
  -- syntactically: `memcmpFlag … (p+1) = memcmpFlag … p &&& (xor;sltiu result)`.
  have hgetp : pb.getD p 0 = pb[p]'hphi := (List.getElem_eq_getD (l := pb) (i := p) 0).symm
  have hgets : sb.getD (off0 + p) 0 = sb[off0 + p]'hshi :=
    (List.getElem_eq_getD (l := sb) (i := off0 + p) 0).symm
  rw [memcmpFlag_succ, hgetp, hgets, ← eq_combo (pb[p]'hphi) (sb[off0 + p]'hshi)]
  -- The concrete straight-line block's output (three scratch registers still
  -- concrete), which we then weaken back to abstract ownership.
  set c29 : Word := ((pb[p]'hphi).zeroExtend 64) ^^^ ((sb[off0 + p]'hshi).zeroExtend 64)
    with hc29
  set c31 : Word :=
    (if BitVec.ult c29 (signExtend12 (1 : BitVec 12)) then (1 : Word) else (0 : Word)) with hc31
  refine cpsTripleWithin_weaken (fun _ h => h)
    (Q := (.x28 ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ (memcmpFlag pb sb off0 p &&& c31))
      ** (.x6 ↦ᵣ (parentBase + BitVec.ofNat 64 (p + 1)))
      ** (.x7 ↦ᵣ (secBase + BitVec.ofNat 64 (off0 + (p + 1))))
      ** (.x29 ↦ᵣ c29) ** (.x30 ↦ᵣ ((sb[off0 + p]'hshi).zeroExtend 64)) ** (.x31 ↦ᵣ c31)
      ** bytesRegion parentBase pb ** bytesRegion secBase sb)
    (fun h hq => ?_)
    (by runBlock hlbu1 hlbu2 hxor hsltiu hand haddi1 haddi2 haddi3 hjal)
  have hq1 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (sepConj_mono (regIs_to_regOwn .x30 _)
          (sepConj_mono (regIs_to_regOwn .x31 _) (fun _ h2 => h2)))))))) h hq
  xperm_hyp hq1
  all_goals exact bytesRegion_pcFree _ _

-- ============================================================================
-- The whole memcmp loop, via `countdownLoop_spec`.
-- ============================================================================

/-- **The memcmp countdown loop** (`0x1000 → 0x1028`): the counter drains from
    `len` to `0`, leaving `mf = memcmpFlag pb sb off0 len` — the running
    bitwise-AND of every per-byte equality over the whole `len`-byte spans.
    Instantiates the register-agnostic `countdownLoop_spec` with the counter
    `x28` and the genuine `memcmpFlag`-fold invariant. -/
theorem memcmpLoop_spec
    (parentBase secBase : Word) (pb sb : List (BitVec 8)) (off0 len : Nat)
    (hlenlt : len < 18446744073709551616)
    (hpblen : pb.length = len)
    (hsblen : off0 + len ≤ sb.length)
    (hpalign : parentBase.toNat % 8 = 0) (hsalign : secBase.toNat % 8 = 0)
    (hpover : parentBase.toNat + len < 2 ^ 64)
    (hsover : secBase.toNat + (off0 + len) < 2 ^ 64)
    (hpvalid : ∀ i, i < len → isValidByteAccess (parentBase + BitVec.ofNat 64 i) = true)
    (hsvalid : ∀ i, i < len →
      isValidByteAccess (secBase + BitVec.ofNat 64 (off0 + i)) = true) :
    cpsTripleWithin (len * (9 + 1) + 1) (0x1000 : Word) (0x1028 : Word) loopCr
      ((.x28 ↦ᵣ BitVec.ofNat 64 len) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** memcmpInv parentBase secBase pb sb off0 len len)
      ((.x28 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** memcmpInv parentBase secBase pb sb off0 len 0) :=
  countdownLoop_spec loopCr (0x1000 : Word) (0x1028 : Word) .x28 (40 : BitVec 13)
    9 len (memcmpInv parentBase secBase pb sb off0 len)
    (by decide)
    hlenlt
    (by decide)
    (fun n => pcFree_memcmpInv parentBase secBase pb sb off0 len n)
    (memAt 0 (0x1000 : Word) (.BEQ .x28 .x0 (40 : BitVec 13)) (by decide) (by decide)
      (by decide) (by rfl))
    (fun n hn => memcmpLoopBody_spec parentBase secBase pb sb off0 len n hn hpblen hsblen
      hpalign hsalign hpover hsover hpvalid hsvalid)

-- ============================================================================
-- The match flag genuinely decides byte-for-byte equality.
-- ============================================================================

/-- `memcmpFlag … p = 1` iff the first `p` byte pairs all agree, else `0`; and
    it is always `0` or `1`.  This ties the loop's numeric accumulator to the
    genuine `is_match` predicate the routine computes. -/
theorem memcmpFlag_eq_one_iff (pb sb : List (BitVec 8)) (off0 : Nat) :
    ∀ p, (memcmpFlag pb sb off0 p = (1 : Word)
            ↔ ∀ k, k < p → pb.getD k 0 = sb.getD (off0 + k) 0)
          ∧ (memcmpFlag pb sb off0 p = 0 ∨ memcmpFlag pb sb off0 p = 1)
  | 0 => ⟨⟨fun _ k hk => absurd hk (by omega), fun _ => rfl⟩, Or.inr rfl⟩
  | p + 1 => by
    obtain ⟨ih_iff, ih01⟩ := memcmpFlag_eq_one_iff pb sb off0 p
    rw [memcmpFlag_succ, eqByteWord]
    by_cases hbyte : pb.getD p 0 = sb.getD (off0 + p) 0
    · rw [if_pos hbyte]
      rcases ih01 with h0 | h1
      · rw [h0]
        refine ⟨⟨fun h => absurd h (by decide), fun hall => ?_⟩, Or.inl (by decide)⟩
        exact absurd (ih_iff.mpr fun k hk => hall k (Nat.lt_succ_of_lt hk)) (by rw [h0]; decide)
      · rw [h1]
        refine ⟨⟨fun _ k hk => ?_, fun _ => by decide⟩, Or.inr (by decide)⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
        · exact ih_iff.mp h1 k hlt
        · subst heq; exact hbyte
    · rw [if_neg hbyte]
      rcases ih01 with h0 | h1
      · rw [h0]
        exact ⟨⟨fun h => absurd h (by decide), fun hall => absurd (hall p (by omega)) hbyte⟩,
          Or.inl (by decide)⟩
      · rw [h1]
        exact ⟨⟨fun h => absurd h (by decide), fun hall => absurd (hall p (by omega)) hbyte⟩,
          Or.inl (by decide)⟩

end ParentHeaderMemcmp
end SAsm
end EvmAsm.Rv64

