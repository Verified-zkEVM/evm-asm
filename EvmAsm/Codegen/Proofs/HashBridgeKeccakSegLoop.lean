/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegLoop

  The gather loops of `zkvm_keccak256_segments` — the part that has no
  counterpart in `zkvm_keccak256` and is therefore the whole reason that
  routine's landed triple does not reach the `tx_signing_hash` lane.

  ## The two loops

  ```
  .Lkss_seg:                       -- KssB+84, OUTER, top-tested on s1 = count
      beq  s1, zero, .Lkss_done
      ld   s5, 0(s0)               -- segment pointer
      ld   s6, 8(s0)               -- segment length
      addi s0, s0, 16 ; addi s1, s1, -1
  .Lkss_byte:                      -- KssB+104, INNER, top-tested on s6 = length
      beq  s6, zero, .Lkss_seg
      lbu  t0, 0(s5)               -- source byte
      add  t1, s3, s4              -- &state[fill]
      lbu  t2, 0(t1) ; xor t2, t2, t0 ; sb t2, 0(t1)
      addi s5, s5, 1 ; addi s6, s6, -1 ; addi s4, s4, 1
      li   t0, 136 ; bne s4, t0, .Lkss_byte
      ...                          -- (rate-block permute; see the DOMAIN note)
  ```

  Both loops are top-tested `BEQ ctr, zero` headers whose bodies return to the
  header, so both are instances of the SAME combinator, `countdownLoop_spec` —
  the inner one exiting to the outer header rather than to a fresh label.

  ## DOMAIN of this module: one rate block

  `KssB+148 … KssB+160` (`csrs 0x800` mid-stream, then `s4 := 0`) is the
  rate-block permute, reached only when the fill counter `s4` hits 136.
  Everything here is proved on the domain **`msg.length ≤ 135`**, on which
  that path is UNREACHED: `s4` is the running count of bytes absorbed, so
  `s4 ≤ 135 < 136` throughout and the `bne s4, t0` at `KssB+144` is always
  taken. That is an INPUT-DOMAIN gate — a genuine restriction on what the
  symbol may be asked, not a missing callee — and it is named as such in the
  registry row. The routine is a leaf; there is no callee anywhere in it.

  ## Why the fill counter and the message index coincide

  On this domain no permute happens, so after `m` absorbed bytes the sponge is
  `xorBytesUpTo keccakZeroStateBytes msg m` and `s4 = m`. The state byte the
  machine XORs into is at offset `s4`, and the source byte is `msg[m]` — the
  SAME index. That is exactly the indexing convention of the landed
  `xorBytesUpTo` (used by `zkvm_keccak256`'s remainder loop), so the pure
  model is shared rather than re-derived, and the digest composes through
  `keccakBodyDigest_eq_specref` (#12104) with `N = 0`, `rem = msg.length`.

  ## Segment ORDER is load-bearing and is pinned

  The post is `keccak256 (segs.flatMap (·.2))` — the concatenation in
  DESCRIPTOR ORDER. `kssSegsIs` lays segment `i` at `segsBase + 16*i` and the
  loop consumes them in increasing address order, so swapping two segments
  changes both the assertion and the digest. Nothing here is symmetric in two
  segments.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegSetup
import EvmAsm.Codegen.Proofs.HashBridgeKeccakRem
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTail
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## Pure model of the gather -/

/-- A segment descriptor: a base pointer and the bytes it covers. -/
abbrev KssSeg := Word × List (BitVec 8)

/-- The message the routine hashes: the concatenation of the segments'
    bytes **in descriptor order**. -/
def kssMsg (segs : List KssSeg) : List (BitVec 8) := segs.flatMap (·.2)

@[simp] theorem kssMsg_nil : kssMsg [] = [] := rfl

@[simp] theorem kssMsg_cons (s : KssSeg) (rest : List KssSeg) :
    kssMsg (s :: rest) = s.2 ++ kssMsg rest := by
  simp [kssMsg]

/-- The descriptor array plus every segment's payload: descriptor `i` occupies
    the two dwords at `base + 16*i`, and its payload lives at the pointer it
    holds. All of it is `**`-separated, so the descriptor array, the payloads
    and (in the caller's frame) the sponge arena are pairwise disjoint — the
    aliasing hazard the routine's docstring flags is excluded by the
    precondition rather than assumed away. -/
def kssSegsIs (base : Word) : List KssSeg → Assertion
  | [] => empAssertion
  | (p, bs) :: rest =>
      (base ↦ₘ p) ** ((base + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
        bytesRegion p bs ** kssSegsIs (base + 16) rest

@[simp] theorem kssSegsIs_nil (base : Word) : kssSegsIs base [] = empAssertion := rfl

@[simp] theorem kssSegsIs_cons (base : Word) (p : Word) (bs : List (BitVec 8))
    (rest : List KssSeg) :
    kssSegsIs base ((p, bs) :: rest) =
      ((base ↦ₘ p) ** ((base + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
        bytesRegion p bs ** kssSegsIs (base + 16) rest) := rfl

theorem kssSegsIs_pcFree (base : Word) (segs : List KssSeg) :
    (kssSegsIs base segs).pcFree := by
  induction segs generalizing base with
  | nil => exact pcFree_emp
  | cons s rest ih =>
    obtain ⟨p, bs⟩ := s
    exact pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) (ih (base + 16))

/-! ## Small arithmetic facts used by the cursor bumps -/

private theorem kss_cursor_bump (p : Word) (k : Nat) :
    p + BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)
      = p + BitVec.ofNat 64 (k + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem kss_ctr_dec (n : Nat) (_hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

private theorem kss_fill_ne_136 (m : Nat) (hm : m ≤ 135) :
    BitVec.ofNat 64 m ≠ (136 : Word) := by
  intro h
  have h1 : (BitVec.ofNat 64 m).toNat = ((136 : Word)).toNat := by rw [h]
  rw [BitVec.toNat_ofNat, show ((136 : Word)).toNat = 136 from rfl,
    Nat.mod_eq_of_lt (by omega)] at h1
  omega

/-! ## The inner byte loop -/

/-- Invariant of the inner loop, indexed by the number of bytes of the current
    segment already CONSUMED. The sponge holds `xorBytesUpTo` of the whole
    message up to global offset `m0 + k`, and `s4` (`x20`) holds exactly that
    offset — the fill/message-index coincidence that only holds because no
    rate-block permute occurs on this domain. -/
def kssInnerInvK (srcPtr : Word) (segBytes msg : List (BitVec 8)) (m0 k : Nat)
    (A : Assertion) : Assertion :=
  (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
    (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) **
    (.x19 ↦ᵣ KssZk3) **
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
    bytesRegion KssZk3 (xorBytesUpTo keccakZeroStateBytes msg (m0 + k)) **
    bytesRegion srcPtr segBytes ** A

theorem kssInnerInvK_pcFree (srcPtr : Word) (segBytes msg : List (BitVec 8))
    (m0 k : Nat) (A : Assertion) (hA : A.pcFree) :
    (kssInnerInvK srcPtr segBytes msg m0 k A).pcFree := by
  simp only [kssInnerInvK]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Length of the running sponge image is always 200. -/
theorem kssState_len (msg : List (BitVec 8)) (m : Nat) :
    (xorBytesUpTo keccakZeroStateBytes msg m).length = 200 := by
  rw [xorBytesUpTo_length]
  exact keccakZeroStateBytes_length

/-- Byte XOR survives the `lbu`(zext64) / `sb`(trunc8) round trip. -/
private theorem kss_trunc_xor (a b : BitVec 8) :
    ((a.zeroExtend 64) ^^^ (b.zeroExtend 64)).truncate 8 = a ^^^ b := by
  have h1 : (a.zeroExtend 64) ^^^ (b.zeroExtend 64) = (a ^^^ b).zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    have ha : a.toNat < 256 := a.isLt
    have hb : b.toNat < 256 := b.isLt
    have ha64 : a.toNat < 2 ^ 64 := by omega
    have hb64 : b.toNat < 2 ^ 64 := by omega
    have hx : a.toNat ^^^ b.toNat < 2 ^ 64 := by
      have := (a ^^^ b).isLt
      have hx8 : a.toNat ^^^ b.toNat < 256 := by rwa [BitVec.toNat_xor] at this
      omega
    simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hx]
  rw [h1, truncate_zeroExtend_byte]

/-- `pcf` extended with `bytesRegion` and an ambient `.pcFree` hypothesis. -/
local macro "pcfa" : tactic =>
  `(tactic| repeat first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _
      | exact kssSegsIs_pcFree _ _
      | assumption)

/-- Peel one owned register off the head of a precondition. -/
private theorem kss_peel1 {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r : Reg}
    (h : ∀ v, cpsTripleWithin n entry exit_ cr ((r ↦ᵣ v) ** P) Q) :
    cpsTripleWithin n entry exit_ cr (regOwn r ** P) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, hA, hB, hdisj, hunion, hpA, hpB⟩ := hPR
  obtain ⟨h1, h2, hd0, hu0, hpOwn, hp2⟩ := hpA
  obtain ⟨v, hv⟩ := hpOwn
  exact h v R hR s hcr
    ⟨hMem, hcompat, hA, hB, hdisj, hunion, ⟨h1, h2, hd0, hu0, hv, hp2⟩, hpB⟩ hpc

/-- Peel two owned registers off the head of a precondition. -/
private theorem kss_peel2 {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 : Reg}
    (h : ∀ v1 v2, cpsTripleWithin n entry exit_ cr
      ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** P) Q) :
    cpsTripleWithin n entry exit_ cr (regOwn r1 ** regOwn r2 ** P) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, hA, hB, hdisj, hunion, hpA, hpB⟩ := hPR
  obtain ⟨a1, s1, d1, u1, ⟨v1, hv1⟩, hr1⟩ := hpA
  obtain ⟨a2, s2, d2, u2, ⟨v2, hv2⟩, hr2⟩ := hr1
  exact h v1 v2 R hR s hcr
    ⟨hMem, hcompat, hA, hB, hdisj, hunion,
      ⟨a1, s1, d1, u1, hv1, ⟨a2, s2, d2, u2, hv2, hr2⟩⟩, hpB⟩ hpc

/-- Peel three owned registers off the head of a precondition. -/
private theorem kss_peel3 {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 r3 : Reg}
    (h : ∀ v1 v2 v3, cpsTripleWithin n entry exit_ cr
      ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** P) Q) :
    cpsTripleWithin n entry exit_ cr
      (regOwn r1 ** regOwn r2 ** regOwn r3 ** P) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, hA, hB, hdisj, hunion, hpA, hpB⟩ := hPR
  obtain ⟨a1, s1, d1, u1, ⟨v1, hv1⟩, hr1⟩ := hpA
  obtain ⟨a2, s2, d2, u2, ⟨v2, hv2⟩, hr2⟩ := hr1
  obtain ⟨a3, s3, d3, u3, ⟨v3, hv3⟩, hr3⟩ := hr2
  exact h v1 v2 v3 R hR s hcr
    ⟨hMem, hcompat, hA, hB, hdisj, hunion,
      ⟨a1, s1, d1, u1, hv1, ⟨a2, s2, d2, u2, hv2, ⟨a3, s3, d3, u3, hv3, hr3⟩⟩⟩,
      hpB⟩ hpc

/-- **One absorbed byte.** `KssB+108 → KssB+104` (ten instructions, the `bne`
    back-edge taken).  `k` bytes of the current segment are already consumed,
    `m0` bytes of the message preceded this segment. -/
theorem kssInnerBody_step (srcPtr : Word) (segBytes msg : List (BitVec 8))
    (m0 k n : Nat) (A : Assertion) (hA : A.pcFree)
    (hk : k < segBytes.length)
    (hbyte : msg.getD (m0 + k) 0 = segBytes[k]'hk)
    (hfill : m0 + k + 1 ≤ 135)
    (hn64 : n + 1 < 2 ^ 64)
    (halignS : srcPtr.toNat % 8 = 0)
    (halignZ : KssZk3.toNat % 8 = 0)
    (hoverS : srcPtr.toNat + k < 2 ^ 64)
    (hoverZ : KssZk3.toNat + (m0 + k) < 2 ^ 64)
    (hvalidS : isValidByteAccess (srcPtr + BitVec.ofNat 64 k) = true)
    (hvalidZ : isValidByteAccess (KssZk3 + BitVec.ofNat 64 (m0 + k)) = true) :
    cpsTripleWithin 10 (KssB + 108) (KssB + 104) kssCr
      ((.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        kssInnerInvK srcPtr segBytes msg m0 k A)
      ((.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        kssInnerInvK srcPtr segBytes msg m0 (k + 1) A) := by
  simp only [kssInnerInvK]
  refine cpsTripleWithin_weaken
    (P := (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
      ((.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 (xorBytesUpTo keccakZeroStateBytes msg (m0 + k)) **
        bytesRegion srcPtr segBytes ** A))
    (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) ?_
  refine kss_peel3 (fun v5 v6 v7 => ?_)
  -- abbreviations
  set ST : List (BitVec 8) := xorBytesUpTo keccakZeroStateBytes msg (m0 + k) with hST
  have hSTlen : ST.length = 200 := kssState_len msg (m0 + k)
  have hidx : m0 + k < ST.length := by omega
  set SB8 : BitVec 8 := segBytes[k]'hk with hSB8
  set ZB8 : BitVec 8 := ST[m0 + k]'hidx with hZB8
  -- 1. LBU t0, 0(s5)  -- source byte
  have c0 := cpsTripleWithin_extend_code
    (kss_mem_at 27 (.LBU .x5 .x21 0) (KssB + 108) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (bytesRegion_lbu_within .x5 .x21 srcPtr v5 (KssB + 108) segBytes k
      (by decide) halignS hk hoverS hvalidS)
  rw [show (KssB + 108 : Word) + 4 = KssB + 112 from by decide] at c0
  -- 2. ADD t1, s3, s4
  have c1 := cpsTripleWithin_extend_code
    (kss_mem_at 28 (.ADD .x6 .x19 .x20) (KssB + 112) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (add_spec_gen_within .x6 .x19 .x20 KssZk3 (BitVec.ofNat 64 (m0 + k)) v6
      (KssB + 112) (by decide))
  rw [show (KssB + 112 : Word) + 4 = KssB + 116 from by decide] at c1
  -- 3. LBU t2, 0(t1)  -- state byte
  have c2 := cpsTripleWithin_extend_code
    (kss_mem_at 29 (.LBU .x7 .x6 0) (KssB + 116) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (bytesRegion_lbu_within .x7 .x6 KssZk3 v7 (KssB + 116) ST (m0 + k)
      (by decide) halignZ hidx hoverZ hvalidZ)
  rw [show (KssB + 116 : Word) + 4 = KssB + 120 from by decide] at c2
  -- 4. XOR t2, t2, t0
  have c3 := cpsTripleWithin_extend_code
    (kss_mem_at 30 (.XOR .x7 .x7 .x5) (KssB + 120) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (xor_spec_gen_rd_eq_rs1_within .x7 .x5 (ZB8.zeroExtend 64) (SB8.zeroExtend 64)
      (KssB + 120) (by decide))
  rw [show (KssB + 120 : Word) + 4 = KssB + 124 from by decide] at c3
  -- 5. SB t2, 0(t1)
  have c4 := cpsTripleWithin_extend_code
    (kss_mem_at 31 (.SB .x6 .x7 0) (KssB + 124) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (bytesRegion_sb_within .x6 .x7 KssZk3
      ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64)) (KssB + 124) ST (m0 + k)
      halignZ hidx hoverZ hvalidZ)
  rw [show (KssB + 124 : Word) + 4 = KssB + 128 from by decide] at c4
  -- 6. ADDI s5, s5, 1
  have c5 := cpsTripleWithin_extend_code
    (kss_mem_at 32 (.ADDI .x21 .x21 (1 : BitVec 12)) (KssB + 128) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (addi_spec_gen_same_within .x21 (srcPtr + BitVec.ofNat 64 k) (1 : BitVec 12)
      (KssB + 128) (by decide))
  rw [kss_cursor_bump srcPtr k,
    show (KssB + 128 : Word) + 4 = KssB + 132 from by decide] at c5
  -- 7. ADDI s6, s6, -1
  have c6 := cpsTripleWithin_extend_code
    (kss_mem_at 33 (.ADDI .x22 .x22 (-1 : BitVec 12)) (KssB + 132) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (addi_spec_gen_same_within .x22 (BitVec.ofNat 64 (n + 1)) (-1 : BitVec 12)
      (KssB + 132) (by decide))
  rw [kss_ctr_dec n hn64,
    show (KssB + 132 : Word) + 4 = KssB + 136 from by decide] at c6
  -- 8. ADDI s4, s4, 1
  have c7 := cpsTripleWithin_extend_code
    (kss_mem_at 34 (.ADDI .x20 .x20 (1 : BitVec 12)) (KssB + 136) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (addi_spec_gen_same_within .x20 (BitVec.ofNat 64 (m0 + k)) (1 : BitVec 12)
      (KssB + 136) (by decide))
  rw [show (BitVec.ofNat 64 (m0 + k) : Word) + signExtend12 (1 : BitVec 12)
        = BitVec.ofNat 64 (m0 + (k + 1)) from by
      have := kss_cursor_bump (0 : Word) (m0 + k)
      simpa using this,
    show (KssB + 136 : Word) + 4 = KssB + 140 from by decide] at c7
  -- 9. LI t0, 136
  have c8 := cpsTripleWithin_extend_code
    (kss_mem_at 35 (.LI .x5 (136 : Word)) (KssB + 140) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (li_spec_gen_within .x5 (SB8.zeroExtend 64) (136 : Word) (KssB + 140)
      (by decide))
  rw [show (KssB + 140 : Word) + 4 = KssB + 144 from by decide] at c8
  -- 10. BNE s4, t0, .Lkss_byte  (taken: fill ≤ 135 ≠ 136)
  have c9br := cpsBranchWithin_extend_code
    (kss_mem_at 36 (.BNE .x20 .x5 (-40 : BitVec 13)) (KssB + 144) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (bne_spec_gen_within .x20 .x5 (-40 : BitVec 13)
      (BitVec.ofNat 64 (m0 + (k + 1))) (136 : Word) (KssB + 144))
  rw [show (KssB + 144 : Word) + signExtend13 (-40 : BitVec 13) = KssB + 104 from
    by decide] at c9br
  have c9 : cpsTripleWithin 1 (KssB + 144) (KssB + 104) kssCr
      ((.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x5 ↦ᵣ (136 : Word)))
      ((.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x5 ↦ᵣ (136 : Word))) := by
    refine cpsBranchWithin_takenStripPure2 c9br (fun _ hQf => ?_)
    obtain ⟨_, _, _, _, _, hBP⟩ := hQf
    exact kss_fill_ne_136 (m0 + k + 1) hfill (((sepConj_pure_right _).1 hBP).2)
  -- the pure sponge step
  have hSTget : ST.getD (m0 + k) 0 = ZB8 := by
    simp only [hZB8, List.getD, List.getElem?_eq_getElem hidx]
    rfl
  have hstep :
      ST.set (m0 + k) (((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64)).truncate 8)
        = xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1)) := by
    rw [kss_trunc_xor]
    show ST.set (m0 + k) (ZB8 ^^^ SB8) = _
    show _ = xorBytesUpTo keccakZeroStateBytes msg ((m0 + k) + 1)
    rw [show xorBytesUpTo keccakZeroStateBytes msg ((m0 + k) + 1)
          = setBytes ST (m0 + k) [(msg.getD (m0 + k) 0) ^^^ (ST.getD (m0 + k) 0)]
        from by rw [hST]; rfl,
      setBytes_singleton, hbyte, hSTget]
    exact congrArg (ST.set (m0 + k)) (BitVec.xor_comm ZB8 SB8)
  -- assemble the ten straight-line steps
  have f01 : cpsTripleWithin 1 (KssB + 108) (KssB + 112) kssCr
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) **
          (.x19 ↦ᵣ KssZk3) ** bytesRegion KssZk3 ST ** A) (by pcfa) c0)
  have f12 : cpsTripleWithin 1 (KssB + 112) (KssB + 116) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) ** (.x7 ↦ᵣ v7) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (SB8.zeroExtend 64)) ** (.x7 ↦ᵣ v7) **
          (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
          bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
        (by pcfa) c1)
  have f23 : cpsTripleWithin 1 (KssB + 116) (KssB + 120) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) ** (.x7 ↦ᵣ v7) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ (ZB8.zeroExtend 64)) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (SB8.zeroExtend 64)) ** (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c2)
  have f34 : cpsTripleWithin 1 (KssB + 120) (KssB + 124) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ (ZB8.zeroExtend 64)) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
        (by pcfa) c3)
  have f45 : cpsTripleWithin 1 (KssB + 124) (KssB + 128) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 ST ** bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A) := by
    rw [← hstep]
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (SB8.zeroExtend 64)) ** (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c4)
  have f56 : cpsTripleWithin 1 (KssB + 128) (KssB + 132) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 k)) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
          (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
          (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion KssZk3
            (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c5)
  have f67 : cpsTripleWithin 1 (KssB + 132) (KssB + 136) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
          (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion KssZk3
            (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c6)
  have f78 : cpsTripleWithin 1 (KssB + 136) (KssB + 140) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + k)) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
          (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
          (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion KssZk3
            (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c7)
  have f89 : cpsTripleWithin 1 (KssB + 140) (KssB + 144) kssCr
      ((.x5 ↦ᵣ (SB8.zeroExtend 64)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A)
      ((.x5 ↦ᵣ (136 : Word)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
          (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion KssZk3
            (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c8)
  have f9e : cpsTripleWithin 1 (KssB + 144) (KssB + 104) kssCr
      ((.x5 ↦ᵣ (136 : Word)) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
        (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A)
      ((.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
        (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
        bytesRegion srcPtr segBytes ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun h hq => ?_)
      (cpsTripleWithin_frameR
        ((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
          (.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
          bytesRegion KssZk3
            (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
          bytesRegion srcPtr segBytes ** A)
        (by pcfa) c9)
    have hq1 :
        ((.x22 ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (.x21 ↦ᵣ (srcPtr + BitVec.ofNat 64 (k + 1))) **
          (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (k + 1))) ** (.x19 ↦ᵣ KssZk3) **
          (.x5 ↦ᵣ (136 : Word)) **
          (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 (m0 + k))) **
          (.x7 ↦ᵣ ((ZB8.zeroExtend 64) ^^^ (SB8.zeroExtend 64))) **
          bytesRegion KssZk3
            (xorBytesUpTo keccakZeroStateBytes msg (m0 + (k + 1))) **
          bytesRegion srcPtr segBytes ** A) h := by
      xperm_hyp hq
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right ?_)))) h hq1
    intro h' hp'
    exact sepConj_mono (regIs_implies_regOwn (r := .x5))
      (fun h'' hp'' => sepConj_mono (regIs_implies_regOwn (r := .x6))
        (fun h₃ hp₃ => sepConj_mono (regIs_implies_regOwn (r := .x7))
          (fun _ => id) h₃ hp₃) h'' hp'') h' hp'
  -- chain
  have g1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) f01 f12
  have g2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g1 f23
  have g3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g2 f34
  have g4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g3 f45
  have g5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g4 f56
  have g6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g5 f67
  have g7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g6 f78
  have g8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g7 f89
  have g9 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) g8 f9e
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (cpsTripleWithin_mono_nSteps (by omega) g9)

/-- **The inner byte loop, whole.** `KssB+104 → KssB+84`: absorb every byte of
    one segment, then fall out to the outer segment header.  `countdownLoop_spec`
    on `s6` (`x22`); the invariant is indexed by bytes REMAINING, so
    `inv n = kssInnerInvK … (L - n)`. -/
theorem kssInnerLoop_spec (srcPtr : Word) (segBytes msg : List (BitVec 8))
    (m0 : Nat) (A : Assertion) (hA : A.pcFree)
    (hL64 : segBytes.length < 18446744073709551616)
    (hmsg : ∀ i, ∀ h : i < segBytes.length,
      msg.getD (m0 + i) 0 = segBytes[i]'h)
    (hfill : m0 + segBytes.length ≤ 135)
    (halignS : srcPtr.toNat % 8 = 0)
    (halignZ : KssZk3.toNat % 8 = 0)
    (hoverS : ∀ i, i < segBytes.length → srcPtr.toNat + i < 2 ^ 64)
    (hoverZ : ∀ i, i < segBytes.length → KssZk3.toNat + (m0 + i) < 2 ^ 64)
    (hvalidS : ∀ i, i < segBytes.length →
      isValidByteAccess (srcPtr + BitVec.ofNat 64 i) = true)
    (hvalidZ : ∀ i, i < segBytes.length →
      isValidByteAccess (KssZk3 + BitVec.ofNat 64 (m0 + i)) = true) :
    cpsTripleWithin (segBytes.length * 11 + 1) (KssB + 104) (KssB + 84) kssCr
      ((.x22 ↦ᵣ BitVec.ofNat 64 segBytes.length) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        kssInnerInvK srcPtr segBytes msg m0 0 A)
      ((.x22 ↦ᵣ BitVec.ofNat 64 0) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        kssInnerInvK srcPtr segBytes msg m0 segBytes.length A) := by
  set L := segBytes.length with hLdef
  have hloop := countdownLoop_spec kssCr (KssB + 104) (KssB + 84) .x22
    (-20 : BitVec 13) 10 L
    (fun n => kssInnerInvK srcPtr segBytes msg m0 (L - n) A)
    (by decide) hL64 (by decide)
    (fun n => kssInnerInvK_pcFree _ _ _ _ _ _ hA)
    (kss_mem_at 26 (.BEQ .x22 .x0 (-20 : BitVec 13)) (KssB + 104) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (fun n hn => by
      have hk : L - (n + 1) < L := by omega
      have hsucc : L - n = (L - (n + 1)) + 1 := by omega
      dsimp only
      rw [hsucc, show (KssB + 104 : Word) + 4 = KssB + 108 from by decide]
      exact kssInnerBody_step srcPtr segBytes msg m0 (L - (n + 1)) n A hA hk
        (hmsg (L - (n + 1)) hk)
        (by omega) (by omega) halignS halignZ
        (hoverS _ hk) (hoverZ _ hk) (hvalidS _ hk) (hvalidZ _ hk))
  dsimp only at hloop
  rw [show L - L = 0 from by omega, show L - 0 = L from by omega] at hloop
  exact cpsTripleWithin_mono_nSteps (by omega) hloop

/-! ## The outer segment loop

    Done by direct induction on the descriptor LIST rather than through a
    counter combinator: `kssSegsIs` is defined by recursion on that list, so the
    cons step unfolds the region split for free and the step budget is allowed
    to depend on the individual segment lengths instead of a uniform bound. -/

/-- Step budget of the outer loop over `segs`: one `beq` for the exhaustion
    test, plus per segment the `beq` + 4-instruction descriptor fetch and the
    inner loop's `11·len + 1`. -/
def kssOuterFuel : List KssSeg → Nat
  | [] => 1
  | (_, bs) :: rest => 6 + bs.length * 11 + kssOuterFuel rest

/-- Everything the outer loop carries across a segment boundary. -/
def kssOuterState (segsBase : Word) (segs : List KssSeg)
    (msg : List (BitVec 8)) (m0 : Nat) (A : Assertion) : Assertion :=
  (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x8 ↦ᵣ segsBase) **
    (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
    ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
    (regOwn .x21) ** (regOwn .x22) **
    bytesRegion KssZk3 (xorBytesUpTo keccakZeroStateBytes msg m0) **
    kssSegsIs segsBase segs ** A

theorem kssOuterState_pcFree (segsBase : Word) (segs : List KssSeg)
    (msg : List (BitVec 8)) (m0 : Nat) (A : Assertion) (hA : A.pcFree) :
    (kssOuterState segsBase segs msg m0 A).pcFree := by
  simp only [kssOuterState]; pcfa

private theorem kss_ofNat_succ_ne_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1) : Word) ≠ (0 : Word) := by
  intro hc
  have h1 : (BitVec.ofNat 64 (n + 1)).toNat = ((0 : Word)).toNat := by rw [hc]
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl,
    Nat.mod_eq_of_lt h] at h1
  omega

/-- Prefix/suffix bookkeeping for the message-index hypothesis. -/
private theorem kss_getD_append_left (bs cs : List (BitVec 8)) (i : Nat)
    (hi : i < bs.length) : (bs ++ cs).getD i 0 = bs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

private theorem kss_getD_append_right (bs cs : List (BitVec 8)) (i : Nat) :
    (bs ++ cs).getD (bs.length + i) 0 = cs.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : bs.length ≤ bs.length + i),
    Nat.add_sub_cancel_left]

/-- **The outer loop, whole.** `KssB+84 → KssB+164`: consume every descriptor
    in order, absorbing each segment's bytes, and fall out to the pad label
    with `s4` holding the total byte count. -/
theorem kssOuterLoop_spec (segsBase : Word) (segs : List KssSeg)
    (msg : List (BitVec 8)) (m0 : Nat) (A : Assertion) (hA : A.pcFree)
    (hcount : segs.length < 2 ^ 64)
    (hsuf : ∀ i, i < (kssMsg segs).length →
      msg.getD (m0 + i) 0 = (kssMsg segs).getD i 0)
    (hfill : m0 + (kssMsg segs).length ≤ 135)
    (halignZ : KssZk3.toNat % 8 = 0)
    (hoverZ : KssZk3.toNat + 200 < 2 ^ 64)
    (hvalidZ : ∀ i, i < 200 →
      isValidByteAccess (KssZk3 + BitVec.ofNat 64 i) = true)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    cpsTripleWithin (kssOuterFuel segs) (KssB + 84) (KssB + 164) kssCr
      (kssOuterState segsBase segs msg m0 A)
      ((.x9 ↦ᵣ BitVec.ofNat 64 0) **
        (.x8 ↦ᵣ (segsBase + BitVec.ofNat 64 (16 * segs.length))) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + (kssMsg segs).length)) **
        (.x19 ↦ᵣ KssZk3) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
        (regOwn .x21) ** (regOwn .x22) **
        bytesRegion KssZk3
          (xorBytesUpTo keccakZeroStateBytes msg (m0 + (kssMsg segs).length)) **
        kssSegsIs segsBase segs ** A) := by
  induction segs generalizing segsBase m0 with
  | nil =>
    -- BEQ s1, zero, +80 taken
    have hbr := cpsBranchWithin_extend_code
      (kss_mem_at 21 (.BEQ .x9 .x0 (80 : BitVec 13)) (KssB + 84) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
      (beq_spec_gen_within .x9 .x0 (80 : BitVec 13)
        (BitVec.ofNat 64 0) (0 : Word) (KssB + 84))
    rw [show (KssB + 84 : Word) + signExtend13 (80 : BitVec 13) = KssB + 164 from
      by decide] at hbr
    have hbt : cpsTripleWithin 1 (KssB + 84) (KssB + 164) kssCr
        ((.x9 ↦ᵣ BitVec.ofNat 64 0) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)))
        ((.x9 ↦ᵣ BitVec.ofNat 64 0) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))) := by
      refine cpsBranchWithin_takenStripPure2 hbr (fun _ hQf => ?_)
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 (by decide)
    have hF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ segsBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
        (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
        (regOwn .x21) ** (regOwn .x22) **
        bytesRegion KssZk3 (xorBytesUpTo keccakZeroStateBytes msg m0) **
        kssSegsIs segsBase [] ** A) (by pcfa) hbt
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_)
      (cpsTripleWithin_mono_nSteps (show 1 ≤ kssOuterFuel [] from by decide) hF)
    · simp only [kssOuterState, List.length_nil] at hp
      xperm_hyp hp
    · simp only [List.length_nil, kssMsg_nil, List.length_nil,
        show 16 * 0 = 0 from rfl, Nat.add_zero]
      rw [show segsBase + BitVec.ofNat 64 0 = segsBase from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega]
      xperm_hyp hq
  | cons s rest ih =>
    obtain ⟨p, bs⟩ := s
    refine cpsTripleWithin_weaken
      (P := (regOwn .x21) ** (regOwn .x22) **
        ((.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 (xorBytesUpTo keccakZeroStateBytes msg m0) **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A))
      (fun _ hp => by
        simp only [kssOuterState, kssSegsIs_cons, List.length_cons] at hp
        xperm_hyp hp)
      (fun _ hq => hq) ?_
    refine kss_peel2 (fun v21 v22 => ?_)
    have hsp := hsegs (p, bs) (List.mem_cons_self ..)
    have halignP : p.toNat % 8 = 0 := hsp.1
    have hbs64 : bs.length < 2 ^ 64 := hsp.2.1
    have hbsv : ∀ i, i < bs.length →
        p.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (p + BitVec.ofNat 64 i) = true := hsp.2.2
    have hrest64 : rest.length < 2 ^ 64 := by
      simp only [List.length_cons] at hcount; omega
    have hcnt64 : rest.length + 1 < 2 ^ 64 := by
      simp only [List.length_cons] at hcount; omega
    -- 1. BEQ s1, zero, +80 NOT taken (count = |rest| + 1 ≠ 0)
    have hbr := cpsBranchWithin_extend_code
      (kss_mem_at 21 (.BEQ .x9 .x0 (80 : BitVec 13)) (KssB + 84) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
      (beq_spec_gen_within .x9 .x0 (80 : BitVec 13)
        (BitVec.ofNat 64 (rest.length + 1)) (0 : Word) (KssB + 84))
    have hbf : cpsTripleWithin 1 (KssB + 84) (KssB + 88) kssCr
        ((.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)))
        ((.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word))) := by
      have h := cpsBranchWithin_ntakenStripPure2 hbr (fun _ hQt => ?_)
      · rwa [show (KssB + 84 : Word) + 4 = KssB + 88 from by decide] at h
      · obtain ⟨_, _, _, _, _, hBP⟩ := hQt
        exact kss_ofNat_succ_ne_zero rest.length hcnt64
          (((sepConj_pure_right _).1 hBP).2)
    -- the ambient carried through this segment's inner loop
    set ST0 : List (BitVec 8) := xorBytesUpTo keccakZeroStateBytes msg m0 with hST0
    set AMB : Assertion :=
      (.x8 ↦ᵣ (segsBase + 16)) ** (.x9 ↦ᵣ BitVec.ofNat 64 rest.length) **
        (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
        kssSegsIs (segsBase + 16) rest ** A with hAMB
    have hAMBpc : AMB.pcFree := by rw [hAMB]; pcfa
    -- flat pre/post shapes at each PC
    have hz0 : segsBase + signExtend12 (0 : BitVec 12) = segsBase := by
      rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega
    have hz8 : segsBase + signExtend12 (8 : BitVec 12) = segsBase + 8 := by
      rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
    have hz16 : segsBase + signExtend12 (16 : BitVec 12) = segsBase + 16 := by
      rw [show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide]
    -- 2. LD s5, 0(s0)
    have e1 := cpsTripleWithin_extend_code
      (kss_mem_at 22 (.LD .x21 .x8 (0 : BitVec 12)) (KssB + 88) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
      (ld_spec_gen_within .x21 .x8 segsBase v21 p (0 : BitVec 12)
        (KssB + 88) (by decide))
    rw [hz0, show (KssB + 88 : Word) + 4 = KssB + 92 from by decide] at e1
    -- 3. LD s6, 8(s0)
    have e2 := cpsTripleWithin_extend_code
      (kss_mem_at 23 (.LD .x22 .x8 (8 : BitVec 12)) (KssB + 92) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
      (ld_spec_gen_within .x22 .x8 segsBase v22
        (BitVec.ofNat 64 bs.length) (8 : BitVec 12) (KssB + 92) (by decide))
    rw [hz8, show (KssB + 92 : Word) + 4 = KssB + 96 from by decide] at e2
    -- 4. ADDI s0, s0, 16
    have e3 := cpsTripleWithin_extend_code
      (kss_mem_at 24 (.ADDI .x8 .x8 (16 : BitVec 12)) (KssB + 96) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
      (addi_spec_gen_same_within .x8 segsBase (16 : BitVec 12) (KssB + 96)
        (by decide))
    rw [hz16, show (KssB + 96 : Word) + 4 = KssB + 100 from by decide] at e3
    -- 5. ADDI s1, s1, -1
    have e4 := cpsTripleWithin_extend_code
      (kss_mem_at 25 (.ADDI .x9 .x9 (-1 : BitVec 12)) (KssB + 100) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
      (addi_spec_gen_same_within .x9 (BitVec.ofNat 64 (rest.length + 1))
        (-1 : BitVec 12) (KssB + 100) (by decide))
    rw [kss_ctr_dec rest.length hcnt64,
      show (KssB + 100 : Word) + 4 = KssB + 104 from by decide] at e4
    -- 6. the inner byte loop for this segment
    have e5 := kssInnerLoop_spec p bs msg m0 AMB hAMBpc hbs64
      (fun i h => by
        have hi : i < (kssMsg ((p, bs) :: rest)).length := by
          rw [kssMsg_cons]; simp only [List.length_append]; omega
        rw [hsuf i hi, kssMsg_cons, kss_getD_append_left bs (kssMsg rest) i h,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        rfl)
      (by
        have : (kssMsg ((p, bs) :: rest)).length = bs.length + (kssMsg rest).length := by
          rw [kssMsg_cons]; simp only [List.length_append]
        omega)
      halignP halignZ
      (fun i hi => (hbsv i hi).1)
      (fun i hi => by
        have h200 : m0 + i < 200 := by
          have : (kssMsg ((p, bs) :: rest)).length = bs.length + (kssMsg rest).length := by
            rw [kssMsg_cons]; simp only [List.length_append]
          omega
        omega)
      (fun i hi => (hbsv i hi).2)
      (fun i hi => hvalidZ (m0 + i) (by
        have : (kssMsg ((p, bs) :: rest)).length = bs.length + (kssMsg rest).length := by
          rw [kssMsg_cons]; simp only [List.length_append]
        omega))
    -- 7. the induction hypothesis on the remaining descriptors
    have hIH := ih (segsBase + 16) (m0 + bs.length) hrest64
      (fun i hi => by
        have hi' : bs.length + i < (kssMsg ((p, bs) :: rest)).length := by
          rw [kssMsg_cons]; simp only [List.length_append]; omega
        rw [show m0 + bs.length + i = m0 + (bs.length + i) from by omega,
          hsuf (bs.length + i) hi', kssMsg_cons,
          kss_getD_append_right bs (kssMsg rest) i])
      (by
        have : (kssMsg ((p, bs) :: rest)).length = bs.length + (kssMsg rest).length := by
          rw [kssMsg_cons]; simp only [List.length_append]
        omega)
      (fun s hs => hsegs s (List.mem_cons_of_mem _ hs))
    -- full-state chain
    have hmsgLen : (kssMsg ((p, bs) :: rest)).length
        = bs.length + (kssMsg rest).length := by
      rw [kssMsg_cons]; simp only [List.length_append]
    set ST1 : List (BitVec 8) :=
      xorBytesUpTo keccakZeroStateBytes msg (m0 + bs.length) with hST1
    have F1 : cpsTripleWithin 1 (KssB + 84) (KssB + 88) kssCr
        ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
        ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x8 ↦ᵣ segsBase) **
            (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
            (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
            bytesRegion KssZk3 ST0 **
            (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
            bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
          (by pcfa) hbf)
    have F2 : cpsTripleWithin 1 (KssB + 88) (KssB + 92) kssCr
        ((.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
        ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ v22) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x22 ↦ᵣ v22) ** (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
            ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
            (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
            bytesRegion KssZk3 ST0 **
            ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
            bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
          (by pcfa) e1)
    have F3 : cpsTripleWithin 1 (KssB + 92) (KssB + 96) kssCr
        ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ v22) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
        ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x21 ↦ᵣ p) ** (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
            ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
            (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
            bytesRegion KssZk3 ST0 ** (segsBase ↦ₘ p) **
            bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
          (by pcfa) e2)
    have F4 : cpsTripleWithin 1 (KssB + 96) (KssB + 100) kssCr
        ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) ** (.x8 ↦ᵣ segsBase) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
        ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
          (.x8 ↦ᵣ (segsBase + 16)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by xperm_hyp hq)
        (cpsTripleWithin_frameR
          ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
            (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
            ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
            (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
            bytesRegion KssZk3 ST0 **
            (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
            bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
          (by pcfa) e3)
    have F5 : cpsTripleWithin 1 (KssB + 100) (KssB + 104) kssCr
        ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
          (.x9 ↦ᵣ BitVec.ofNat 64 (rest.length + 1)) **
          (.x8 ↦ᵣ (segsBase + 16)) **
          (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          bytesRegion KssZk3 ST0 **
          (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
          bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
        ((.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          kssInnerInvK p bs msg m0 0 AMB) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => ?_)
        (cpsTripleWithin_frameR
          ((.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
            (.x8 ↦ᵣ (segsBase + 16)) **
            (.x20 ↦ᵣ BitVec.ofNat 64 m0) ** (.x19 ↦ᵣ KssZk3) **
            ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
            (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
            bytesRegion KssZk3 ST0 **
            (segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
            bytesRegion p bs ** kssSegsIs (segsBase + 16) rest ** A)
          (by pcfa) e4)
      simp only [kssInnerInvK, hAMB,
        show p + BitVec.ofNat 64 0 = p from by
          rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega,
        show m0 + 0 = m0 from rfl, ← hST0]
      xperm_hyp hq
    have F6 : cpsTripleWithin (bs.length * 11 + 1) (KssB + 104) (KssB + 84) kssCr
        ((.x22 ↦ᵣ BitVec.ofNat 64 bs.length) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          kssInnerInvK p bs msg m0 0 AMB)
        (kssOuterState (segsBase + 16) rest msg (m0 + bs.length) A **
          ((segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
            bytesRegion p bs)) := by
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) e5
      simp only [kssInnerInvK, hAMB] at hq
      have hq1 :
          ((.x21 ↦ᵣ (p + BitVec.ofNat 64 bs.length)) **
            (.x22 ↦ᵣ BitVec.ofNat 64 0) **
            ((.x9 ↦ᵣ BitVec.ofNat 64 rest.length) **
              (.x8 ↦ᵣ (segsBase + 16)) **
              (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + bs.length)) **
              (.x19 ↦ᵣ KssZk3) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
              (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
              bytesRegion KssZk3 ST1 **
              kssSegsIs (segsBase + 16) rest ** A **
              ((segsBase ↦ₘ p) **
                ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
                bytesRegion p bs))) h := by
        xperm_hyp hq
      have hq2 :
          ((regOwn .x21) ** (regOwn .x22) **
            ((.x9 ↦ᵣ BitVec.ofNat 64 rest.length) **
              (.x8 ↦ᵣ (segsBase + 16)) **
              (.x20 ↦ᵣ BitVec.ofNat 64 (m0 + bs.length)) **
              (.x19 ↦ᵣ KssZk3) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
              (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
              bytesRegion KssZk3 ST1 **
              kssSegsIs (segsBase + 16) rest ** A **
              ((segsBase ↦ₘ p) **
                ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
                bytesRegion p bs))) h :=
        sepConj_mono (regIs_implies_regOwn (r := .x21))
          (fun h' hp' => sepConj_mono (regIs_implies_regOwn (r := .x22))
            (fun _ => id) h' hp') h hq1
      simp only [kssOuterState, ← hST1]
      xperm_hyp hq2
    have F7 := cpsTripleWithin_frameR
      ((segsBase ↦ₘ p) ** ((segsBase + 8) ↦ₘ BitVec.ofNat 64 bs.length) **
        bytesRegion p bs) (by pcfa) hIH
    have G1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) F1 F2
    have G2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) G1 F3
    have G3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) G2 F4
    have G4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) G3 F5
    have G5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) G4 F6
    have G6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) G5 F7
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_)
      (cpsTripleWithin_mono_nSteps
        (show 1 + 1 + 1 + 1 + 1 + (bs.length * 11 + 1) + kssOuterFuel rest
          ≤ kssOuterFuel ((p, bs) :: rest) from by
          simp only [kssOuterFuel]; omega) G6)
    simp only [kssSegsIs_cons, List.length_cons, hmsgLen,
      show 16 * (rest.length + 1) = 16 * rest.length + 16 from by omega]
    rw [show segsBase + BitVec.ofNat 64 (16 * rest.length + 16)
          = segsBase + 16 + BitVec.ofNat 64 (16 * rest.length) from by
        rw [show (BitVec.ofNat 64 (16 * rest.length + 16) : Word)
              = BitVec.ofNat 64 (16 * rest.length) + 16 from by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              show ((16 : Word)).toNat = 16 from rfl]
            omega]
        bv_omega,
      show m0 + (bs.length + (kssMsg rest).length)
          = m0 + bs.length + (kssMsg rest).length from by omega]
    xperm_hyp hq

end EvmAsm.Codegen.Proofs
