/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTop

  **`zkvm_keccak256_segments`, whole routine, at its linked guest address.**

  The scatter-gather keccak entry point: given a `(ptr, len)` descriptor array
  (`a0`), its element count (`a1`) and a 32-byte output buffer (`a2`), it hashes
  the CONCATENATION of the segments' bytes without materialising it, carrying
  the 0..135 rate-block fill offset in `s4` across segment boundaries, and
  writes `keccak256` of that concatenation to `a2`.

  This is the entry point `tx_signing_hash` — and hence the EIP-7702
  authorization digest — reaches keccak through; it is NOT `zkvm_keccak256`,
  which is why the landed `zkvm_keccak256_spec_within` does not cover it.

  ## The one gate is an INPUT-DOMAIN gate, not a callee

  `zkvm_keccak256_segments` is a **leaf**: it calls nothing.  Its only
  non-local instruction is `csrs 0x800`, the Keccak-f accelerator, which the
  machine model executes as an in-place 25-lane permutation — a memory effect,
  not a control transfer.  So `kssCr = CodeReq.ofProg KssB kssProgL` covers
  every address the routine executes and this triple carries **no unproven-callee
  dependency**.

  The primary claim is the ungated multi-rate triple
  `zkvm_keccak256_segments_spec_within` (`kssAbsorbed` / `kssFill` /
  `kssInnerLoop_spec_multi` / `kssOuterLoop_spec_multi`). A short-domain
  special case `…_within_short` (`hshort : |msg| ≤ 135`) is retained for
  recovery against the older `xorBytesUpTo` model.

  ## The keccak leg REDUCES; it is not assumed

  `kssDigest_eq_specref_any` below is a proof, not a hypothesis: the operational
  sponge image the machine leaves in the output buffer is shown equal to
  `Stateless.SpecRef.keccak256` by routing through the landed, UNCONDITIONAL
  bridge `keccakBodyDigest_eq_specref` (#12104).  The post is therefore stated
  in pure SpecRef terms.

  ## Segment ORDER is pinned

  The post is `keccak256 (kssMsg segs)` — the concatenation in DESCRIPTOR
  ORDER — and `kss_sample_witness` instantiates it at three segments of
  different lengths whose concatenation `[0x01, 0x02, 0x03, 0x04]` is not
  symmetric in any two of them.

  No elaboration budget is widened here beyond `maxRecDepth`.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegLoop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTail
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## The pure reduction: guest sponge image = `SpecRef.keccak256` -/

theorem kssRemAbsorbed_eq (st0 inp : List (BitVec 8)) (rem : Nat) :
    keccakRemAbsorbed st0 inp rem = xorBytesUpTo st0 inp rem := by
  rcases Nat.eq_zero_or_pos rem with h | h
  · subst h; rfl
  · exact keccakRemAbsorbed_pos st0 inp rem h

theorem kssPrePad_eq (msg : List (BitVec 8)) :
    keccakBodyPrePad msg 0 msg.length
      = xorBytesUpTo keccakZeroStateBytes msg msg.length := by
  simp only [keccakBodyPrePad, keccakAbsorbedPrefix, Nat.mul_zero,
    List.drop_zero, List.take_length, kssRemAbsorbed_eq]

/-- ⭐ **The keccak leg, reduced.** The 32 bytes the routine copies out of the
    sponge are exactly `SpecRef.keccak256` of the gathered message — via the
    landed `keccakBodyDigest_eq_specref` (#12104) at `N = 0`. -/
theorem kssDigest_eq_specref (msg : List (BitVec 8)) (hshort : msg.length ≤ 135) :
    keccakDigestCopy
        (kssFinalState (xorBytesUpTo keccakZeroStateBytes msg msg.length)
          msg.length)
      = Stateless.SpecRef.keccak256 msg := by
  have hb := keccakBodyDigest_eq_specref msg 0 msg.length
    (by simp only [keccakAbsorbStep, Nat.mul_zero, Nat.zero_add])
    (by simp only [keccakAbsorbStep]; omega)
  rw [← hb]
  simp only [keccakBodyDigest, kssFinalState, kssPrePad_eq]

/-! ## Register bookkeeping -/

/-- Exposed temporaries that pass through the whole routine owned. Together
    with `x11`/`x12` (the ABI arguments the routine consumes) these are exactly
    the tail's `kssTailOwns`. -/
def kssFreeTemps : List Reg :=
  [.x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]

theorem kssTailOwns_eq : kssTailOwns = .x11 :: .x12 :: kssFreeTemps := rfl

theorem kssRateCsrsSans_eq : kssRateCsrsSans = .x11 :: .x12 :: kssFreeTemps := rfl

theorem kssRateCsrsSans_eq_tail : kssRateCsrsSans = kssTailOwns := rfl

/-- Entry values of the ABI-frame registers. -/
def kssEntryVals (ret v8 v9 v18 v19 v20 v21 v22 : Word) : Reg → Word
  | .x1 => ret
  | .x8 => v8
  | .x9 => v9
  | .x18 => v18
  | .x19 => v19
  | .x20 => v20
  | .x21 => v21
  | .x22 => v22
  | _ => (0 : Word)

private abbrev kssFrameRegsIs (vals : Reg → Word) : Assertion :=
  (.x1 ↦ᵣ vals .x1) ** (.x8 ↦ᵣ vals .x8) ** (.x9 ↦ᵣ vals .x9) **
    (.x18 ↦ᵣ vals .x18) ** (.x19 ↦ᵣ vals .x19) ** (.x20 ↦ᵣ vals .x20) **
    (.x21 ↦ᵣ vals .x21) ** (.x22 ↦ᵣ vals .x22)

private abbrev kssFrameRegsOwn : Assertion :=
  (regOwn .x1) ** (regOwn .x8) ** (regOwn .x9) ** (regOwn .x18) **
    (regOwn .x19) ** (regOwn .x20) ** (regOwn .x21) ** (regOwn .x22)

private theorem kssRegsAt_flat (vals : Reg → Word) :
    regsAt kssFrame vals = kssFrameRegsIs vals := by
  simp only [kssFrameRegsIs, kssFrame, regsAt, List.foldr, sepConj_emp_right']

private theorem kssRegsOwnAt_flat : regsOwnAt kssFrame = kssFrameRegsOwn := by
  simp only [kssFrameRegsOwn, kssFrame, regsOwnAt, List.foldr, sepConj_emp_right']

/-- Demote a head run of concrete register atoms to ownership. -/
private theorem kss_own1 {r : Reg} {v : Word} {R : Assertion} :
    ∀ h, ((r ↦ᵣ v) ** R) h → ((regOwn r) ** R) h :=
  fun h hp => sepConj_mono (regIs_implies_regOwn (r := r)) (fun _ => id) h hp

private theorem kss_own2 {r1 r2 : Reg} {v1 v2 : Word} {R : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** R) h →
      ((regOwn r1) ** (regOwn r2) ** R) h :=
  fun h hp => sepConj_mono (regIs_implies_regOwn (r := r1))
    (fun h' hp' => kss_own1 h' hp') h hp

private theorem kss_own3 {r1 r2 r3 : Reg} {v1 v2 v3 : Word} {R : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** R) h →
      ((regOwn r1) ** (regOwn r2) ** (regOwn r3) ** R) h :=
  fun h hp => sepConj_mono (regIs_implies_regOwn (r := r1))
    (fun h' hp' => kss_own2 h' hp') h hp

private theorem kss_own5 {r1 r2 r3 r4 r5 : Reg} {v1 v2 v3 v4 v5 : Word}
    {R : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
        (r5 ↦ᵣ v5) ** R) h →
      ((regOwn r1) ** (regOwn r2) ** (regOwn r3) ** (regOwn r4) **
        (regOwn r5) ** R) h :=
  fun h hp => sepConj_mono (regIs_implies_regOwn (r := r1))
    (fun h' hp' => sepConj_mono (regIs_implies_regOwn (r := r2))
      (fun h'' hp'' => kss_own3 h'' hp'') h' hp') h hp

private theorem kss_own6 {r1 r2 r3 r4 r5 r6 : Reg} {v1 v2 v3 v4 v5 v6 : Word}
    {R : Assertion} :
    ∀ h, ((r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3) ** (r4 ↦ᵣ v4) **
        (r5 ↦ᵣ v5) ** (r6 ↦ᵣ v6) ** R) h →
      ((regOwn r1) ** (regOwn r2) ** (regOwn r3) ** (regOwn r4) **
        (regOwn r5) ** (regOwn r6) ** R) h :=
  fun h hp => sepConj_mono (regIs_implies_regOwn (r := r1))
    (fun h' hp' => kss_own5 h' hp') h hp


/-- Pack ABI `x10`/`x11`/`x12` plus `kssFreeTemps` into the multi-rate
    outer-loop CSRS ownership (`own x10 ** regOwns kssRateCsrsSans`). -/
private theorem kss_pack_x10_sans (v10 v11 v12 : Word) (R : Assertion) :
    ∀ h, ((.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
        regOwns kssFreeTemps ** R) h →
      ((regOwn .x10) ** regOwns kssRateCsrsSans ** R) h := by
  intro h hs
  have hs1 := kss_own1 h hs
  have hs2 :
      ((.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** regOwns kssFreeTemps **
        (regOwn .x10) ** R) h := by
    xperm_hyp hs1
  have hs3 : ((regOwn .x11) ** (regOwn .x12) ** regOwns kssFreeTemps **
      (regOwn .x10) ** R) h :=
    kss_own2 h hs2
  have hs4 :
      ((regOwn .x10) **
        ((regOwn .x11) ** (regOwn .x12) ** regOwns kssFreeTemps) ** R) h := by
    xperm_hyp hs3
  simpa [kssRateCsrsSans_eq, regOwns] using hs4

/-- `pcf` extended with the region predicates this module uses. -/
local macro "pcfk" : tactic =>
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
      | exact pcFree_regOwns _
      | assumption)

/-! ## Caller-visible pre / post -/

/-- Caller-visible precondition. The ABI-frame registers (`ra`, `s0`–`s6`) are
    NOT here — `abiFrame_spec_own` supplies them as `regsAt kssFrame vals`. -/
def kssCallerPre (segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 : Word) (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) **
    (.x12 ↦ᵣ outputBase) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
    (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    regOwns kssFreeTemps **
    bytesRegion KssZk3 os **
    bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)) **
    kssSegsIs segsBase segs ** A

theorem kssCallerPre_pcFree (segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 : Word) (A : Assertion) (hA : A.pcFree) :
    (kssCallerPre segsBase outputBase segs os v5 v6 v7 A).pcFree := by
  simp only [kssCallerPre]; pcfk

/-- Caller-visible postcondition: success status, the digest in the output
    buffer stated in pure SpecRef terms, the sponge arena left holding the
    final permuted state, and the descriptor array + payloads intact.

    Every cell the routine writes is named here: `a0`, the 32-byte output
    buffer and the 200-byte `zk3_state` arena. Nothing else is touched, so no
    universally quantified frame can refute this post. -/
def kssCallerPost (segsBase outputBase : Word) (segs : List KssSeg)
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (regOwn .x11) ** (regOwn .x12) **
    ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
    regOwns kssFreeTemps **
    bytesRegion KssZk3
      (kssFinalState
        (xorBytesUpTo keccakZeroStateBytes (kssMsg segs) (kssMsg segs).length)
        (kssMsg segs).length) **
    bytesRegion outputBase (Stateless.SpecRef.keccak256 (kssMsg segs)) **
    kssSegsIs segsBase segs ** A

theorem kssCallerPost_pcFree (segsBase outputBase : Word) (segs : List KssSeg)
    (A : Assertion) (hA : A.pcFree) :
    (kssCallerPost segsBase outputBase segs A).pcFree := by
  simp only [kssCallerPost]; pcfk

/-- Multi-rate caller-visible post: sponge is `kssAbsorbed` then pad/permute
    at `kssFill`, digest via `kssDigest_eq_specref_any`. -/
def kssCallerPost_multi (segsBase outputBase : Word) (segs : List KssSeg)
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ (0 : Word)) ** (regOwn .x11) ** (regOwn .x12) **
    ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
    (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
    regOwns kssFreeTemps **
    bytesRegion KssZk3
      (kssFinalState
        (kssAbsorbed (kssMsg segs) (kssMsg segs).length)
        (kssFill (kssMsg segs).length)) **
    bytesRegion outputBase (Stateless.SpecRef.keccak256 (kssMsg segs)) **
    kssSegsIs segsBase segs ** A

theorem kssCallerPost_multi_pcFree (segsBase outputBase : Word)
    (segs : List KssSeg) (A : Assertion) (hA : A.pcFree) :
    (kssCallerPost_multi segsBase outputBase segs A).pcFree := by
  simp only [kssCallerPost_multi]; pcfk


/-! ## The body: `KssB+36` (body entry) → `KssB+240` (body exit) -/

theorem kssXorZero (msg : List (BitVec 8)) :
    xorBytesUpTo keccakZeroStateBytes msg 0 = keccakZeroStateBytes := rfl

/-- Body step budget: setup (3+2+2+100+1) ;; outer gather ;; tail (20). -/
def kssBodyFuel (segs : List KssSeg) : Nat := 128 + kssOuterFuel segs

theorem kssBodyCore_spec (ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (hos : os.length = 200)
    (hshort : (kssMsg segs).length ≤ 135)
    (hcount : segs.length < 2 ^ 64)
    (halignZ : KssZk3.toNat % 8 = 0)
    (hoverZ : KssZk3.toNat + 200 < 2 ^ 64)
    (hvalidZb : ∀ i, i < 200 →
      isValidByteAccess (KssZk3 + BitVec.ofNat 64 i) = true)
    (hvalidZm : ∀ j, j < 200 →
      isValidMemAddr (KssZk3 + BitVec.ofNat 64 j) = true)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    cpsTripleWithin (kssBodyFuel segs) (KssB + 36) (KssB + 240) kssCr
      (kssFrameRegsIs (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      (kssFrameRegsOwn ** kssCallerPost segsBase outputBase segs A) := by
  set msg : List (BitVec 8) := kssMsg segs with hmsg
  set L : Nat := msg.length with hL
  set out0 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8) with hout0
  set STL : List (BitVec 8) := xorBytesUpTo keccakZeroStateBytes msg L with hSTL
  have hSTLlen : STL.length = 200 := kssState_len msg L
  have hmsgL : (kssMsg segs).length ≤ 135 := hshort
  have hLshort : L ≤ 135 := hshort
  -- the caller-visible ambient carried through the outer gather
  set AOut : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      (.x18 ↦ᵣ outputBase) ** regOwns kssFreeTemps **
      bytesRegion outputBase out0 ** A with hAOut
  have hAOutPc : AOut.pcFree := by rw [hAOut]; pcfk
  -- the caller-visible ambient carried through the tail
  set ATail : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x9 ↦ᵣ BitVec.ofNat 64 0) **
      (.x8 ↦ᵣ (segsBase + BitVec.ofNat 64 (16 * segs.length))) **
      (regOwn .x21) ** (regOwn .x22) ** kssSegsIs segsBase segs ** A with hATail
  have hATailPc : ATail.pcFree := by rw [hATail]; pcfk
  -- ---- setup: KssB+36 → KssB+84 ----
  have s1 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 os **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk)
    (kssSetupMoves_spec segsBase (BitVec.ofNat 64 segs.length) outputBase
      v8 v9 v18)
  have s2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 os **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssSetupLa_spec v19)
  have s3 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 os **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssSetupZeroPrep_spec v5 v6)
  have s4 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      (.x7 ↦ᵣ v7) ** (.x19 ↦ᵣ KssZk3) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssZeroLoop_spec os hos halignZ hoverZ)
  have s5 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ (KssZk3 + BitVec.ofNat 64 200)) ** (.x6 ↦ᵣ BitVec.ofNat 64 0) **
      (.x7 ↦ᵣ v7) ** (.x19 ↦ᵣ KssZk3) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 keccakZeroStateBytes **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssFillInit_spec v20)
  have g1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 s2
  have g2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) g1 s3
  have g3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) g2 s4
  have g4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) g3 s5
  -- reshape the setup exit into the outer loop's entry state
  have gSetup : cpsTripleWithin 108 (KssB + 36) (KssB + 84) kssCr
      (kssFrameRegsIs (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      (kssOuterState segsBase segs msg 0 AOut) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_) g4
    · simp only [kssFrameRegsIs, kssCallerPre, kssEntryVals, ← hout0] at hp
      xperm_hyp hp
    · have hq1 :
          ((.x5 ↦ᵣ (KssZk3 + BitVec.ofNat 64 200)) **
            (.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x7 ↦ᵣ v7) **
            (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
            ((.x9 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x8 ↦ᵣ segsBase) **
              (.x20 ↦ᵣ BitVec.ofNat 64 0) ** (.x19 ↦ᵣ KssZk3) **
              ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion KssZk3 keccakZeroStateBytes **
              kssSegsIs segsBase segs **
              ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
                (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) **
                (.x12 ↦ᵣ outputBase) ** (.x18 ↦ᵣ outputBase) **
                regOwns kssFreeTemps **
                bytesRegion outputBase out0 ** A))) h := by
        xperm_hyp hq
      have hq2 := kss_own5 h hq1
      simp only [kssOuterState, kssXorZero, hAOut]
      xperm_hyp hq2
  -- ---- outer gather: KssB+84 → KssB+164 ----
  have gOuter := kssOuterLoop_spec segsBase segs msg 0 AOut hAOutPc hcount
    (fun i _ => by rw [Nat.zero_add])
    (by simp only [Nat.zero_add]; exact hmsgL)
    halignZ hoverZ hvalidZb hsegs
  -- ---- tail: KssB+164 → KssB+240 ----
  have gTail := kssTail_spec outputBase STL L ATail hATailPc hSTLlen
    (by omega) halignZ (by omega)
    (hvalidZb L (by omega)) (hvalidZb 135 (by omega)) hvalidZm
  -- glue outer → tail
  have gOT : cpsTripleWithin (kssOuterFuel segs + 20) (KssB + 84) (KssB + 240)
      kssCr (kssOuterState segsBase segs msg 0 AOut)
      ((.x20 ↦ᵣ BitVec.ofNat 64 L) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion KssZk3 (kssFinalState STL L) **
        kssTailAmb outputBase (keccakDigestCopy (kssFinalState STL L)) ATail) :=
    cpsTripleWithin_seq_perm_same_cr
      (fun h hq => by
        rw [Nat.zero_add] at hq
        simp only [hAOut] at hq
        have hq1 :
            ((.x10 ↦ᵣ segsBase) ** (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) **
              (.x12 ↦ᵣ outputBase) **
              ((.x20 ↦ᵣ BitVec.ofNat 64 L) ** (regOwn .x5) ** (regOwn .x6) **
                (regOwn .x7) ** bytesRegion KssZk3 STL **
                (.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
                ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
                regOwns kssFreeTemps ** bytesRegion outputBase out0 **
                ((.x1 ↦ᵣ ret) ** (.x9 ↦ᵣ BitVec.ofNat 64 0) **
                  (.x8 ↦ᵣ (segsBase + BitVec.ofNat 64 (16 * segs.length))) **
                  (regOwn .x21) ** (regOwn .x22) **
                  kssSegsIs segsBase segs ** A))) h := by
          xperm_hyp hq
        have hq2 := kss_own3 h hq1
        simp only [kssTailAmb, kssTailOwns_eq, regOwns_cons, hATail, ← hout0]
        xperm_hyp hq2)
      gOuter gTail
  -- glue setup → (outer ;; tail), then reshape into the caller post
  have gAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) gSetup gOT
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps
      (show 108 + (kssOuterFuel segs + 20) ≤ kssBodyFuel segs from by
        simp only [kssBodyFuel]; omega) gAll)
  simp only [kssTailAmb, kssTailOwns_eq, regOwns_cons, hATail] at hq
  rw [kssDigest_eq_specref msg (by omega)] at hq
  have hq1 :
      ((.x1 ↦ᵣ ret) ** (.x8 ↦ᵣ (segsBase + BitVec.ofNat 64 (16 * segs.length))) **
        (.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x18 ↦ᵣ outputBase) **
        (.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 L) **
        ((regOwn .x21) ** (regOwn .x22) **
          (.x10 ↦ᵣ (0 : Word)) ** (regOwn .x11) ** (regOwn .x12) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          regOwns kssFreeTemps **
          bytesRegion KssZk3 (kssFinalState STL L) **
          bytesRegion outputBase (Stateless.SpecRef.keccak256 msg) **
          kssSegsIs segsBase segs ** A)) h := by
    xperm_hyp hq
  have hq2 := kss_own6 h hq1
  simp only [kssFrameRegsOwn, kssCallerPost, ← hmsg, ← hL, ← hSTL]
  xperm_hyp hq2

/-! ## `zk3_state` is inside the RAM zone -/

theorem kssZk3_toNat : KssZk3.toNat = 2745483488 := by decide

theorem kssZk3_valid_mem (i : Nat) (hi : i < 200) :
    isValidMemAddr (KssZk3 + BitVec.ofNat 64 i) = true := by
  have hnat : (KssZk3 + BitVec.ofNat 64 i).toNat = 2745483488 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show GuestAddrs.zk3_state % 2 ^ 64 = 2745483488 from by decide,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  simp only [isValidMemAddr, hnat, MEM_START, MEM_END, INPUT_MEM_START,
    INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨by omega, by omega⟩

theorem kssZk3_valid_byte (i : Nat) (hi : i < 200) :
    isValidByteAccess (KssZk3 + BitVec.ofNat 64 i) = true :=
  kssZk3_valid_mem i hi

/-! ## ⭐ The whole-routine triple -/

/-- **`zkvm_keccak256_segments`, whole routine, at `GuestAddrs.zkvm_keccak256_segments`.**

    From the linked entry over the emitted 70-instruction program itself
    (`kssCr = CodeReq.ofProg KssB kssProgL`), execution returns to the caller
    having written `SpecRef.keccak256` of the segments' concatenation — in
    DESCRIPTOR ORDER — to the `a2` buffer, with `a0 = 0`.

    The prologue/epilogue, the callee-saved round trip and the `sp` restore are
    DERIVED from `kssProg_eq_abiFrame` via `abiFrame_spec_own`, not assumed.

    ⛔ There is NO unproven-callee dependency: the routine is a leaf.
    The ONE gate is the INPUT-DOMAIN restriction `hshort` — the single
    rate-block domain `≤ 135` bytes total. Every other hypothesis is a
    resource/ABI fact: the 200-byte sponge arena, region alignment and
    memory validity, a two-byte-aligned return address, and u64
    representability of the counts. -/
theorem zkvm_keccak256_segments_spec_within_short
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hshort : (kssMsg segs).length ≤ 135)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let vals := kssEntryVals ret v8 v9 v18 v19 v20 v21 v22
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuel segs) KssB ret kssCr
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost segsBase outputBase segs A) := by
  intro vals newSp
  have hcore := kssBodyCore_spec ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA hos hshort hcount
    (by decide) (by decide) kssZk3_valid_byte kssZk3_valid_mem hsegs
  have hslots : (frameSlotsSaved kssFrame newSp vals).pcFree :=
    pcFree_frameSlotsSaved _ _ _
  have hcoreF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** frameSlotsSaved kssFrame newSp vals)
    (pcFree_sepConj (by pcf) hslots) hcore
  have hbody : cpsTripleWithin (kssBodyFuel segs)
      (KssB + BitVec.ofNat 64 (4 * (1 + kssFrame.length)))
      (KssB + BitVec.ofNat 64 (4 * (1 + kssFrame.length + kssBody.length)))
      kssCr
      ((.x2 ↦ᵣ newSp) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      ((.x2 ↦ᵣ newSp) ** regsOwnAt kssFrame **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost segsBase outputBase segs A) := by
    rw [kssBodyEntry_eq, kssBodyExit_eq]
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hcoreF
    · rw [kssRegsAt_flat] at hp
      xperm_hyp hp
    · rw [kssRegsOwnAt_flat]
      xperm_hyp hq
  have habi := abiFrame_spec_own KssB sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    kssFrame (0 : BitVec 12)
    [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48),
      (.x22, 56)]
    vals kssBody (kssBodyFuel segs)
    (kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
    (kssCallerPost segsBase outputBase segs A) kssCr
    rfl (by decide) (by decide)
    (by rw [kssProg_eq_abiFrame]; exact kssProgL_bound)
    rfl halign_ret
    (by
      rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
        show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]
      bv_omega)
    (kssCallerPre_pcFree _ _ _ _ _ _ _ _ hA)
    (kssCallerPost_pcFree _ _ _ _ hA)
    (by rw [kssProg_eq_abiFrame]; exact fun a i h => h)
    hbody
  exact cpsTripleWithin_mono_nSteps
    (show 1 + kssFrame.length + kssBodyFuel segs + kssFrame.length + 1 + 1
      ≤ 19 + kssBodyFuel segs from by rw [kssFrame_len]; omega) habi

/-! ## ⭐ A compiled satisfying instance: the three-segment gather -/

/-- The sample descriptor array: three segments of DIFFERENT lengths at three
    distinct dword-aligned RAM pointers. -/
def kssSampleSegs : List KssSeg :=
  [((0xa1000000 : Word), [(0x01 : BitVec 8)]),
   ((0xa1000008 : Word), [(0x02 : BitVec 8), (0x03 : BitVec 8)]),
   ((0xa1000010 : Word), [(0x04 : BitVec 8)])]

/-- **Segment ORDER is pinned concretely.** The gathered message is the
    descriptor-order concatenation; it is not symmetric in any two segments,
    so swapping two of them changes the digest this triple claims. -/
theorem kss_sample_msg :
    kssMsg kssSampleSegs
      = [(0x01 : BitVec 8), (0x02 : BitVec 8), (0x03 : BitVec 8),
         (0x04 : BitVec 8)] := by decide

/-- ⭐ **Non-vacuity: a closed instantiation of the whole-routine triple.**

    Three segments — the shape `tx_signing_hash` uses — at concrete
    dword-aligned RAM addresses, a concrete even return address, a zeroed
    200-byte sponge arena and a zeroed 32-byte output buffer. EVERY hypothesis
    of `zkvm_keccak256_segments_spec_within_short` is discharged here by a
    closed proof, so the theorem is not vacuously true on an unsatisfiable
    hypothesis set, and the 3-segment gather is inside the claim. -/
theorem kss_sample_witness :
    let vals := kssEntryVals (0x80000100 : Word) 0 0 0 0 0 0 0
    let newSp := (0xa1010000 : Word) + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuel kssSampleSegs) KssB (0x80000100 : Word)
      kssCr
      (((.x2 : Reg) ↦ᵣ (0xa1010000 : Word)) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre (0xa1001000 : Word) (0xa1002000 : Word) kssSampleSegs
          (List.replicate 200 (0 : BitVec 8)) 0 0 0 empAssertion)
      (((.x2 : Reg) ↦ᵣ (0xa1010000 : Word)) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost (0xa1001000 : Word) (0xa1002000 : Word) kssSampleSegs
          empAssertion) :=
  zkvm_keccak256_segments_spec_within_short (0xa1010000 : Word)
    (0x80000100 : Word) (0xa1001000 : Word) (0xa1002000 : Word) kssSampleSegs
    (List.replicate 200 (0 : BitVec 8)) 0 0 0 0 0 0 0 0 0 0
    empAssertion pcFree_emp (by decide)
    (by simp only [List.length_replicate])
    (by decide) (by decide) (by decide)


/-- Body step budget on the multi-rate path: setup (108) ;; outer gather ;; tail (20). -/
def kssBodyFuelMulti (segs : List KssSeg) : Nat := 128 + kssOuterFuelMulti segs

theorem kssBodyCore_spec_multi (ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (halignZ : KssZk3.toNat % 8 = 0)
    (hoverZ : KssZk3.toNat + 200 < 2 ^ 64)
    (hvalidZb : ∀ i, i < 200 →
      isValidByteAccess (KssZk3 + BitVec.ofNat 64 i) = true)
    (hvalidZm : ∀ j, j < 200 →
      isValidMemAddr (KssZk3 + BitVec.ofNat 64 j) = true)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    cpsTripleWithin (kssBodyFuelMulti segs) (KssB + 36) (KssB + 240) kssCr
      (kssFrameRegsIs (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      (kssFrameRegsOwn ** kssCallerPost_multi segsBase outputBase segs A) := by
  set msg : List (BitVec 8) := kssMsg segs with hmsg
  set L : Nat := msg.length with hL
  set out0 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8) with hout0
  set STL : List (BitVec 8) := kssAbsorbed msg L with hSTL
  have hSTLlen : STL.length = 200 := kssAbsorbed_state_len msg L
  have hfillL : kssFill L ≤ 135 :=
    Nat.lt_succ_iff.mp (by simpa [keccakAbsorbStep] using kssFill_lt L)
  set AOut : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x18 ↦ᵣ outputBase) **
      bytesRegion outputBase out0 ** A with hAOut
  have hAOutPc : AOut.pcFree := by rw [hAOut]; pcfk
  set ATail : Assertion :=
    (.x1 ↦ᵣ ret) ** (.x9 ↦ᵣ BitVec.ofNat 64 0) **
      (.x8 ↦ᵣ (segsBase + BitVec.ofNat 64 (16 * segs.length))) **
      (regOwn .x21) ** (regOwn .x22) ** kssSegsIs segsBase segs ** A with hATail
  have hATailPc : ATail.pcFree := by rw [hATail]; pcfk
  have s1 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 os **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk)
    (kssSetupMoves_spec segsBase (BitVec.ofNat 64 segs.length) outputBase
      v8 v9 v18)
  have s2 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 os **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssSetupLa_spec v19)
  have s3 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ v7) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 os **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssSetupZeroPrep_spec v5 v6)
  have s4 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      (.x7 ↦ᵣ v7) ** (.x19 ↦ᵣ KssZk3) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) **
      (.x20 ↦ᵣ v20) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssZeroLoop_spec os hos halignZ hoverZ)
  have s5 := cpsTripleWithin_frameR
    ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
      (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x12 ↦ᵣ outputBase) **
      ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
      (.x5 ↦ᵣ (KssZk3 + BitVec.ofNat 64 200)) **
      (.x6 ↦ᵣ BitVec.ofNat 64 0) **
      (.x7 ↦ᵣ v7) ** (.x19 ↦ᵣ KssZk3) **
      (.x8 ↦ᵣ segsBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 segs.length) **
      (.x18 ↦ᵣ outputBase) ** (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
      regOwns kssFreeTemps ** bytesRegion KssZk3 keccakZeroStateBytes **
      bytesRegion outputBase out0 ** kssSegsIs segsBase segs ** A)
    (by pcfk) (kssFillInit_spec v20)
  have g1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 s2
  have g2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) g1 s3
  have g3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) g2 s4
  have g4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) g3 s5
  have gSetup : cpsTripleWithin 108 (KssB + 36) (KssB + 84) kssCr
      (kssFrameRegsIs (kssEntryVals ret v8 v9 v18 v19 v20 v21 v22) **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      (kssOuterStateMulti segsBase segs msg 0 AOut) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun h hq => ?_) g4
    · simp only [kssFrameRegsIs, kssCallerPre, kssEntryVals, ← hout0] at hp
      xperm_hyp hp
    · have hq1 :
          ((.x5 ↦ᵣ (KssZk3 + BitVec.ofNat 64 200)) **
            (.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x7 ↦ᵣ v7) **
            (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
            ((.x9 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x8 ↦ᵣ segsBase) **
              (.x20 ↦ᵣ BitVec.ofNat 64 0) ** (.x19 ↦ᵣ KssZk3) **
              ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion KssZk3 keccakZeroStateBytes **
              kssSegsIs segsBase segs **
              ((.x1 ↦ᵣ ret) ** (.x10 ↦ᵣ segsBase) **
                (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) **
                (.x12 ↦ᵣ outputBase) ** (.x18 ↦ᵣ outputBase) **
                regOwns kssFreeTemps **
                bytesRegion outputBase out0 ** A))) h := by
        xperm_hyp hq
      have hq2 := kss_own5 h hq1
      have hq3 :
          ((.x10 ↦ᵣ segsBase) **
            (.x11 ↦ᵣ BitVec.ofNat 64 segs.length) **
            (.x12 ↦ᵣ outputBase) ** regOwns kssFreeTemps **
            ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
              (regOwn .x21) ** (regOwn .x22) **
              ((.x9 ↦ᵣ BitVec.ofNat 64 segs.length) ** (.x8 ↦ᵣ segsBase) **
                (.x20 ↦ᵣ BitVec.ofNat 64 0) ** (.x19 ↦ᵣ KssZk3) **
                ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
                bytesRegion KssZk3 keccakZeroStateBytes **
                kssSegsIs segsBase segs **
                ((.x1 ↦ᵣ ret) ** (.x18 ↦ᵣ outputBase) **
                  bytesRegion outputBase out0 ** A)))) h := by
        xperm_hyp hq2
      have hq4 := kss_pack_x10_sans segsBase (BitVec.ofNat 64 segs.length)
        outputBase _ h hq3
      simp only [kssOuterStateMulti, kssAbsorbed_zero, hAOut]
      rw [show kssFill 0 = 0 from rfl]
      xperm_hyp hq4
  have gOuter := kssOuterLoop_spec_multi segsBase segs msg 0 AOut hAOutPc hcount
    (fun i _ => by rw [Nat.zero_add])
    (by simp only [Nat.zero_add]; exact Nat.le_refl _)
    halignZ hoverZ hvalidZb hvalidZm hsegs
  have gTail := kssTail_spec outputBase STL (kssFill L) ATail hATailPc hSTLlen
    hfillL halignZ (by omega)
    (hvalidZb (kssFill L)
      (Nat.lt_trans (kssFill_lt L)
        (by decide : keccakAbsorbStep < 200)))
    (hvalidZb 135 (by omega)) hvalidZm
  have gOT : cpsTripleWithin (kssOuterFuelMulti segs + 20) (KssB + 84) (KssB + 240)
      kssCr (kssOuterStateMulti segsBase segs msg 0 AOut)
      ((.x20 ↦ᵣ BitVec.ofNat 64 (kssFill L)) ** (regOwn .x5) **
        (regOwn .x6) ** (regOwn .x7) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion KssZk3 (kssFinalState STL (kssFill L)) **
        kssTailAmb outputBase
          (keccakDigestCopy (kssFinalState STL (kssFill L))) ATail) :=
    cpsTripleWithin_seq_perm_same_cr
      (fun h hq => by
        rw [Nat.zero_add] at hq
        simp only [hAOut] at hq
        rw [kssRateCsrsSans_eq_tail] at hq
        simp only [kssTailAmb, hATail, ← hout0]
        xperm_hyp hq)
      gOuter gTail
  have gAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) gSetup gOT
  refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps
      (show 108 + (kssOuterFuelMulti segs + 20) ≤ kssBodyFuelMulti segs from by
        simp only [kssBodyFuelMulti]; omega) gAll)
  simp only [kssTailAmb, kssTailOwns_eq, regOwns_cons, hATail] at hq
  rw [kssDigest_eq_specref_any msg] at hq
  have hq1 :
      ((.x1 ↦ᵣ ret) **
        (.x8 ↦ᵣ (segsBase + BitVec.ofNat 64 (16 * segs.length))) **
        (.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x18 ↦ᵣ outputBase) **
        (.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 (kssFill L)) **
        ((regOwn .x21) ** (regOwn .x22) **
          (.x10 ↦ᵣ (0 : Word)) ** (regOwn .x11) ** (regOwn .x12) **
          ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
          (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          regOwns kssFreeTemps **
          bytesRegion KssZk3 (kssFinalState STL (kssFill L)) **
          bytesRegion outputBase (Stateless.SpecRef.keccak256 msg) **
          kssSegsIs segsBase segs ** A)) h := by
    xperm_hyp hq
  have hq2 := kss_own6 h hq1
  simp only [kssFrameRegsOwn, kssCallerPost_multi, ← hmsg, ← hL, ← hSTL]
  xperm_hyp hq2

/-- **`zkvm_keccak256_segments`, whole routine, multi-rate.** Same ABI-frame
    wrapping as the short-domain theorem, without the `hshort` gate. -/
theorem zkvm_keccak256_segments_spec_within
    (sp0 ret segsBase outputBase : Word) (segs : List KssSeg)
    (os : List (BitVec 8)) (v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hos : os.length = 200)
    (hcount : segs.length < 2 ^ 64)
    (hsegs : ∀ s ∈ segs, s.1.toNat % 8 = 0 ∧ s.2.length < 2 ^ 64 ∧
      (∀ i, i < s.2.length →
        s.1.toNat + i < 2 ^ 64 ∧
        isValidByteAccess (s.1 + BitVec.ofNat 64 i) = true)) :
    let vals := kssEntryVals ret v8 v9 v18 v19 v20 v21 v22
    let newSp := sp0 + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuelMulti segs) KssB ret kssCr
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      ((.x2 ↦ᵣ sp0) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost_multi segsBase outputBase segs A) := by
  intro vals newSp
  have hcore := kssBodyCore_spec_multi ret segsBase outputBase segs os
    v5 v6 v7 v8 v9 v18 v19 v20 v21 v22 A hA hos hcount
    (by decide) (by decide) kssZk3_valid_byte kssZk3_valid_mem hsegs
  have hslots : (frameSlotsSaved kssFrame newSp vals).pcFree :=
    pcFree_frameSlotsSaved _ _ _
  have hcoreF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** frameSlotsSaved kssFrame newSp vals)
    (pcFree_sepConj (by pcf) hslots) hcore
  have hbody : cpsTripleWithin (kssBodyFuelMulti segs)
      (KssB + BitVec.ofNat 64 (4 * (1 + kssFrame.length)))
      (KssB + BitVec.ofNat 64 (4 * (1 + kssFrame.length + kssBody.length)))
      kssCr
      ((.x2 ↦ᵣ newSp) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
      ((.x2 ↦ᵣ newSp) ** regsOwnAt kssFrame **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost_multi segsBase outputBase segs A) := by
    rw [kssBodyEntry_eq, kssBodyExit_eq]
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hcoreF
    · rw [kssRegsAt_flat] at hp
      xperm_hyp hp
    · rw [kssRegsOwnAt_flat]
      xperm_hyp hq
  have habi := abiFrame_spec_own KssB sp0 ret (-64 : BitVec 12) (64 : BitVec 12)
    kssFrame (0 : BitVec 12)
    [(.x8, 8), (.x9, 16), (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48),
      (.x22, 56)]
    vals kssBody (kssBodyFuelMulti segs)
    (kssCallerPre segsBase outputBase segs os v5 v6 v7 A)
    (kssCallerPost_multi segsBase outputBase segs A) kssCr
    rfl (by decide) (by decide)
    (by rw [kssProg_eq_abiFrame]; exact kssProgL_bound)
    rfl halign_ret
    (by
      rw [show signExtend12 (-64 : BitVec 12) = (-64 : Word) from by decide,
        show signExtend12 (64 : BitVec 12) = (64 : Word) from by decide]
      bv_omega)
    (kssCallerPre_pcFree _ _ _ _ _ _ _ _ hA)
    (kssCallerPost_multi_pcFree _ _ _ _ hA)
    (by rw [kssProg_eq_abiFrame]; exact fun a i h => h)
    hbody
  exact cpsTripleWithin_mono_nSteps
    (show 1 + kssFrame.length + kssBodyFuelMulti segs + kssFrame.length + 1 + 1
      ≤ 19 + kssBodyFuelMulti segs from by rw [kssFrame_len]; omega) habi

/-- Multi-rate non-vacuity: the same 3-segment gather, ungated. -/
theorem kss_sample_witness_multi :
    let vals := kssEntryVals (0x80000100 : Word) 0 0 0 0 0 0 0
    let newSp := (0xa1010000 : Word) + signExtend12 ((-64 : BitVec 12))
    cpsTripleWithin (19 + kssBodyFuelMulti kssSampleSegs) KssB (0x80000100 : Word)
      kssCr
      (((.x2 : Reg) ↦ᵣ (0xa1010000 : Word)) ** regsAt kssFrame vals **
        frameSlotsOwn kssFrame newSp **
        kssCallerPre (0xa1001000 : Word) (0xa1002000 : Word) kssSampleSegs
          (List.replicate 200 (0 : BitVec 8)) 0 0 0 empAssertion)
      (((.x2 : Reg) ↦ᵣ (0xa1010000 : Word)) ** regsAt kssFrame vals **
        frameSlotsSaved kssFrame newSp vals **
        kssCallerPost_multi (0xa1001000 : Word) (0xa1002000 : Word) kssSampleSegs
          empAssertion) :=
  zkvm_keccak256_segments_spec_within (0xa1010000 : Word)
    (0x80000100 : Word) (0xa1001000 : Word) (0xa1002000 : Word) kssSampleSegs
    (List.replicate 200 (0 : BitVec 8)) 0 0 0 0 0 0 0 0 0 0
    empAssertion pcFree_emp (by decide)
    (by simp only [List.length_replicate])
    (by decide) (by decide)

end EvmAsm.Codegen.Proofs
