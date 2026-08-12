/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegments

  Proof boundary for the linked `zkvm_keccak256_segments` routine.

  The segment entry is the machine side consumed by the signing-hash
  contracts.  The concrete setup slice lives in the imported prelude; the
  descriptor/byte-loop proof remains tied to the same linked `CodeReq` so that
  the eventual top-level triple cannot silently prove a different program.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegmentsPrelude
import EvmAsm.Codegen.Proofs.HashBridgeKeccakZero
import EvmAsm.Codegen.Proofs.HashBridgeKeccakAbsorb
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256_segments
private abbrev segmentsProgL : List Instr := zkvmKeccak256Segments_prog
private abbrev segmentsCr : CodeReq := CodeReq.ofProg B segmentsProgL

private theorem segmentsProgL_len : segmentsProgL.length = 70 := by
  simp only [segmentsProgL, zkvmKeccak256Segments_prog,
    zkvmKeccak256Segments_prog_of]
  decide

private theorem segmentsProgL_bound : 4 * segmentsProgL.length < 2 ^ 64 := by
  rw [segmentsProgL_len]
  norm_num

private theorem segments_mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < segmentsProgL.length)
    (hins : segmentsProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → segmentsCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A segmentsProgL k ins hA hk hins
      segmentsProgL_bound a i h

/-! ## One-byte segment body

The byte body is deliberately stated independently of the two control
branches around it.  The header tests the segment remainder, while the
following `BNE x20,x5` tests the rate offset; keeping both tests outside this
lemma prevents the two counters from being accidentally conflated.
-/

def xorBytesAt (st inp : List (BitVec 8)) (off : Nat) : Nat → List (BitVec 8)
  | 0 => st
  | q + 1 =>
      let st' := xorBytesAt st inp off q
      let b := (inp.getD q 0) ^^^ (st'.getD (off + q) 0)
      setBytes st' (off + q) [b]

theorem xorBytesAt_length (st inp : List (BitVec 8)) (off q : Nat) :
    (xorBytesAt st inp off q).length = st.length := by
  induction q generalizing st with
  | zero => rfl
  | succ q ih =>
    simp only [xorBytesAt, length_setBytes, ih]

private theorem xorBytesAt_succ (st inp : List (BitVec 8)) (off k : Nat)
    (hkState : off + k < (xorBytesAt st inp off k).length)
    (hkInp : k < inp.length) :
    xorBytesAt st inp off (k + 1) =
      setBytes (xorBytesAt st inp off k) (off + k)
        [(inp[k]'hkInp) ^^^ (xorBytesAt st inp off k).getD (off + k) 0] := by
  rw [show k + 1 = Nat.succ k by omega]
  simp only [xorBytesAt, setBytes_singleton]
  have hinpD : inp.getD k 0 = inp[k]'hkInp := by
    simp [List.getD_eq_getElem?_getD, hkInp]
  have hstD : (xorBytesAt st inp off k).getD (off + k) 0 =
      (xorBytesAt st inp off k)[off + k]'hkState := by
    simp [List.getD_eq_getElem?_getD, hkState]
  rw [hinpD, hstD]

private def segmentsByteStep (st inp : List (BitVec 8)) (off cursor : Nat) :
    List (BitVec 8) :=
  setBytes st off [(inp.getD cursor 0) ^^^ (st.getD off 0)]

private theorem segmentsByteStep_eq_xor (st inp : List (BitVec 8))
    (off cursor : Nat) :
    segmentsByteStep st inp off cursor =
      xorBytesAt st (inp.drop cursor) off 1 := by
  simp [segmentsByteStep, xorBytesAt, List.getD_eq_getElem?_getD]

private theorem segmentsByteStep_xorBytesAt_succ
    (st inp : List (BitVec 8)) (off k : Nat)
    (hkState : off + k < (xorBytesAt st inp off k).length)
    (hkInp : k < inp.length) :
    segmentsByteStep (xorBytesAt st inp off k) inp (off + k) k =
      xorBytesAt st inp off (k + 1) := by
  have hxor := xorBytesAt_succ st inp off k hkState hkInp
  simp only [segmentsByteStep, List.getD_eq_getElem?_getD]
  rw [hxor]
  congr 1
  simp [hkState, hkInp]

private def segmentsStateFold (st inp : List (BitVec 8))
    (off cursor q : Nat) : List (BitVec 8) :=
  match q with
  | 0 => st
  | q + 1 =>
      let st' := segmentsByteStep st inp off cursor
      if off + 1 = 136 then
        segmentsStateFold (setBytes st' 0 (keccakBytes st' 0)) inp 0 (cursor + 1) q
      else
        segmentsStateFold st' inp (off + 1) (cursor + 1) q

private theorem segmentsStateFold_succ (st inp : List (BitVec 8))
    (off cursor q : Nat) :
    segmentsStateFold st inp off cursor (q + 1) =
      let st' := segmentsByteStep st inp off cursor
      if off + 1 = 136 then
        segmentsStateFold (setBytes st' 0 (keccakBytes st' 0)) inp 0 (cursor + 1) q
      else
        segmentsStateFold st' inp (off + 1) (cursor + 1) q := by
  rfl

private theorem segmentsStateFold_nonrate_step (st inp : List (BitVec 8))
    (off cursor : Nat) (hneq : off + 1 ≠ 136) :
    segmentsStateFold st inp off cursor 1 =
      xorBytesAt st (inp.drop cursor) off 1 := by
  simp [segmentsStateFold, hneq, segmentsByteStep_eq_xor]

private theorem segmentsStateFold_rate_boundary (st inp : List (BitVec 8))
    (cursor : Nat) :
    segmentsStateFold st inp 135 cursor 1 =
      setBytes (segmentsByteStep st inp 135 cursor) 0
        (keccakBytes (segmentsByteStep st inp 135 cursor) 0) := by
  simp [segmentsStateFold]

private theorem segmentsStateFold_rate_boundary_eq_xor
    (st inp : List (BitVec 8)) (cursor : Nat) :
    segmentsStateFold st inp 135 cursor 1 =
      setBytes (xorBytesAt st (inp.drop cursor) 135 1) 0
        (keccakBytes (xorBytesAt st (inp.drop cursor) 135 1) 0) := by
  rw [segmentsStateFold_rate_boundary, segmentsByteStep_eq_xor]

/-! The fill counter is a second state dimension of the fold.  Keeping its
    transition explicit lets the descriptor proof restart a byte loop after a
    rate permutation without pretending that the fill offset is the global
    message index. -/

private def segmentsFillAfter (off : Nat) : Nat → Nat
  | 0 => off
  | q + 1 =>
      let off' := if off + 1 = 136 then 0 else off + 1
      segmentsFillAfter off' q

private theorem segmentsFillAfter_succ (off q : Nat) :
    segmentsFillAfter off (q + 1) =
      segmentsFillAfter (if off + 1 = 136 then 0 else off + 1) q := by
  rfl

private theorem segmentsStateFold_decompose (st inp : List (BitVec 8))
    (off cursor q r : Nat) :
    segmentsStateFold st inp off cursor (q + r) =
      segmentsStateFold
        (segmentsStateFold st inp off cursor q)
        inp (segmentsFillAfter off q) (cursor + q) r := by
  induction q generalizing st off cursor with
  | zero => simp [segmentsStateFold, segmentsFillAfter]
  | succ q ih =>
      let st' := segmentsByteStep st inp off cursor
      by_cases hrate : off + 1 = 136
      · simp only [Nat.succ_add, segmentsStateFold, hrate, ↓reduceIte,
          segmentsFillAfter]
        rw [ih (st := setBytes st' 0 (keccakBytes st' 0))
          (off := 0) (cursor := cursor + 1)]
        dsimp [st']
        rw [show cursor + 1 + q = cursor + (q + 1) by omega]
      · simp only [Nat.succ_add, segmentsStateFold, hrate, ↓reduceIte,
          segmentsFillAfter]
        rw [ih (st := st') (off := off + 1) (cursor := cursor + 1)]
        dsimp [st']
        rw [show cursor + 1 + q = cursor + (q + 1) by omega]

private theorem segmentsFillAfter_lt (off q : Nat) (hoff : off < 136) :
    segmentsFillAfter off q < 136 := by
  induction q generalizing off with
  | zero => exact hoff
  | succ q ih =>
      simp only [segmentsFillAfter]
      split <;> apply ih <;> omega

private theorem segmentsStateFold_step (st inp : List (BitVec 8))
    (off cursor q : Nat) :
    segmentsStateFold st inp off cursor (q + 1) =
      let stq := segmentsStateFold st inp off cursor q
      let fill := segmentsFillAfter off q
      let st' := segmentsByteStep stq inp fill (cursor + q)
      if fill + 1 = 136 then
        setBytes st' 0 (keccakBytes st' 0)
      else st' := by
  rw [segmentsStateFold_decompose st inp off cursor q 1]
  rfl

private theorem segments_cursor_advance (p : Word) (k : Nat)
    (_hk : k + 1 < 2 ^ 64) :
    p + BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12) =
      p + BitVec.ofNat 64 (k + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem segments_counter_decrement (n k : Nat)
    (_hk : k + 1 ≤ n) (_hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - k) + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 (n - (k + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  have hklt : n - k < 2 ^ 64 := by omega
  have hpos : n - k ≥ 1 := by omega
  omega

private theorem segments_byte_xor (a b : BitVec 8) :
    ((a.zeroExtend 64) ^^^ (b.zeroExtend 64)).truncate 8 = a ^^^ b := by
  have h1 : (a.zeroExtend 64) ^^^ (b.zeroExtend 64) =
      (a ^^^ b).zeroExtend 64 := by
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

private theorem segments_values_to_owns3 {P : Assertion} {v5 v6 v7 : Word} :
    ∀ h, (P ** ((.x5 ↦ᵣ v5) ** ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7)))) h →
      (P ** (regOwn .x5 ** (regOwn .x6 ** regOwn .x7))) h := by
  intro h hp
  exact sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (regIs_implies_regOwn .x7))) h hp

private theorem segments_byte_body_step (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st inp : List (BitVec 8))
    (off n k : Nat) (v5 v6 v7 : Word)
    (hk : k < n) (hoff : off < 136)
    (hst : st.length = 200) (hinp : n ≤ inp.length)
    (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + off < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 off) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hmemIn : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i →
      cr a = some i)
    (hmemAdd : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i →
      cr a = some i)
    (hmemState : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i →
      cr a = some i)
    (hmemStore : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i →
      cr a = some i)
    (hmemInputStep : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i →
      cr a = some i)
    (hmemCountStep : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i →
      cr a = some i)
    (hmemOffsetStep : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i →
      cr a = some i) :
    cpsTripleWithin 8 hdr (hdr + 32) cr
      ((.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 off)) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase st **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7))
      ((.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 (off + 1))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
        bytesRegion scratchBase (segmentsByteStep st inp off k) **
        bytesRegion inputBase inp **
        (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7)) := by
  have hk_in : k < inp.length := Nat.lt_of_lt_of_le hk hinp
  have hk_state : off < st.length := by
    rw [hst]
    omega
  have hlbuIn := cpsTripleWithin_extend_code hmemIn
    (bytesRegion_lbu_within .x5 .x21 inputBase v5 hdr inp k
      (by decide) hb8i hk_in hbaseI hvalidI)
  have hlbuInF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase st **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7)) (by pcf) hlbuIn
  have c0 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hlbuInF
  have hAdd := cpsTripleWithin_extend_code hmemAdd
    (add_spec_gen_within .x6 .x19 .x20 scratchBase
      (BitVec.ofNat 64 off) v6 (hdr + 4) (by decide))
  rw [show (hdr + 4 : Word) + 4 = hdr + 8 by
    rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]] at hAdd
  have hAddF := cpsTripleWithin_frameR
    ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase st **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ ((inp[k]'hk_in).zeroExtend 64)) **
      (.x7 ↦ᵣ v7)) (by pcf) hAdd
  have c1 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hAddF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have hstate := cpsTripleWithin_extend_code hmemState
    (bytesRegion_lbu_within .x7 .x6 scratchBase v7 (hdr + 8)
      st off (by decide) hb8s hk_state
      hbaseS hvalidS)
  rw [show (hdr + 8 : Word) + 4 = hdr + 12 by
    rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]] at hstate
  have hstateF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) ** bytesRegion inputBase inp **
      (.x5 ↦ᵣ ((inp[k]'hk_in).zeroExtend 64))) (by pcf) hstate
  have c2 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hstateF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  let vState : Word := (st[off]'hk_state).zeroExtend 64
  let vInput : Word := (inp[k]'hk_in).zeroExtend 64
  have hx := cpsTripleWithin_extend_code hmemXor
    (xor_spec_gen_rd_eq_rs1_within .x7 .x5 vState vInput
      (hdr + 12) (by decide))
  rw [show (hdr + 12 : Word) + 4 = hdr + 16 by
    rw [BitVec.add_assoc, show ((12 : Word) + 4) = (16 : Word) from by decide]] at hx
  have hxF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase st **
      bytesRegion inputBase inp ** (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 off))) (by pcf) hx
  have c3 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hxF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  let vX : Word := vState ^^^ vInput
  let st1 : List (BitVec 8) :=
    st.set off (vX.truncate 8)
  have hstore := cpsTripleWithin_extend_code hmemStore
    (bytesRegion_sb_within .x6 .x7 scratchBase vX (hdr + 16)
      st off hb8s hk_state hbaseS hvalidS)
  rw [show (hdr + 16 : Word) + 4 = hdr + 20 by
    rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]] at hstore
  have hstoreF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ ((inp[k]'hk_in).zeroExtend 64))) (by pcf) hstore
  have c4 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hstoreF
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by sep_perm hp) c0123 c4
  have hi := cpsTripleWithin_extend_code hmemInputStep
    (addi_spec_gen_same_within .x21 (inputBase + BitVec.ofNat 64 k)
      (1 : BitVec 12) (hdr + 20) (by decide))
  rw [show (hdr + 20 : Word) + 4 = hdr + 24 by
    rw [BitVec.add_assoc, show ((20 : Word) + 4) = (24 : Word) from by decide]] at hi
  have hk64 : k + 1 < 2 ^ 64 := by omega
  rw [segments_cursor_advance inputBase k hk64] at hi
  have hiF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - k)) **
      bytesRegion scratchBase st1 **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ vInput) **
      (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) ** (.x7 ↦ᵣ vX))
    (by pcf) hi
  have c5 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hiF
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01234 c5
  have hc := cpsTripleWithin_extend_code hmemCountStep
    (addi_spec_gen_same_within .x22 (BitVec.ofNat 64 (n - k))
      (-1 : BitVec 12) (hdr + 24) (by decide))
  rw [show (hdr + 24 : Word) + 4 = hdr + 28 by
    rw [BitVec.add_assoc, show ((24 : Word) + 4) = (28 : Word) from by decide]] at hc
  rw [segments_counter_decrement n k (by omega) hn64] at hc
  have hcF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      bytesRegion scratchBase st1 **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ vInput) **
      (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) ** (.x7 ↦ᵣ vX))
    (by pcf) hc
  have c6 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hcF
  have c0123456 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012345 c6
  have ho := cpsTripleWithin_extend_code hmemOffsetStep
    (addi_spec_gen_same_within .x20 (BitVec.ofNat 64 off)
      (1 : BitVec 12) (hdr + 28) (by decide))
  rw [show (hdr + 28 : Word) + 4 = hdr + 32 by
    rw [BitVec.add_assoc, show ((28 : Word) + 4) = (32 : Word) from by decide]] at ho
  have hoff_step : BitVec.ofNat 64 off + signExtend12 (1 : BitVec 12) =
      BitVec.ofNat 64 (off + 1) := by
    rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [hoff_step] at ho
  have hoF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ scratchBase) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - (k + 1))) **
      bytesRegion scratchBase st1 **
      bytesRegion inputBase inp ** (.x5 ↦ᵣ vInput) **
      (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) ** (.x7 ↦ᵣ vX))
    (by pcf) ho
  have c7 := cpsTripleWithin_weaken (fun _ hp => by sep_perm hp)
    (fun _ hq => by sep_perm hq) hoF
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123456 c7
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h_state hq => ?_) c
  · rw [show (off + 1) = off + 1 by omega]
    have hbyte : st[off]'hk_state =
        st.getD off 0 := by simp [List.getD_eq_getElem?_getD, hk_state]
    have hbyteval : vX.truncate 8 =
        (inp[k]'hk_in) ^^^ st.getD off 0 := by
      dsimp [vX, vState, vInput]
      change
        (((st[off]'hk_state).zeroExtend 64) ^^^
            ((inp[k]'hk_in).zeroExtend 64)).truncate 8 =
          (inp[k]'hk_in) ^^^ st.getD off 0
      calc
        _ = st[off]'hk_state ^^^ (inp[k]'hk_in) :=
          segments_byte_xor _ _
        _ = (inp[k]'hk_in) ^^^ st[off]'hk_state :=
          BitVec.xor_comm _ _
        _ = (inp[k]'hk_in) ^^^ st.getD off 0 := by
          rw [hbyte]
    have hst1 : st1 = segmentsByteStep st inp off k := by
      unfold st1 segmentsByteStep
      rw [hbyteval]
      congr 1
      simp [List.getD_eq_getElem?_getD, hk_in, hk_state]
    rw [hst1] at hq
    rw [show off + 1 = off + 1 by omega] at hq
    let Pseg : Assertion :=
      (.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 (off + 1)) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      (.x22 ↦ᵣ BitVec.ofNat 64 (n - (k + 1))) **
      bytesRegion scratchBase (segmentsByteStep st inp off k) **
      bytesRegion inputBase inp
    have hq0 :
        (Pseg ** (.x5 ↦ᵣ vInput) **
          (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
          (.x7 ↦ᵣ vX)) h_state := by
      have hq1 :
          (((.x19 ↦ᵣ scratchBase) **
            (.x20 ↦ᵣ BitVec.ofNat 64 (off + 1)) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ BitVec.ofNat 64 (n - (k + 1))) **
            bytesRegion scratchBase (segmentsByteStep st inp off k) **
            bytesRegion inputBase inp **
            (.x5 ↦ᵣ vInput) **
            (.x6 ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
            (.x7 ↦ᵣ vX))) h_state := by
        xperm_hyp hq
      simpa only [Pseg, sepConj_assoc'] using hq1
    simpa only [Pseg, sepConj_assoc'] using
      (segments_values_to_owns3 (P := Pseg)
        (v5 := vInput) (v6 := scratchBase + BitVec.ofNat 64 off)
        (v7 := vX) h_state hq0)

private theorem segments_rate_test_spec (cr : CodeReq) (hdr vOffset : Word)
    (A : Assertion) (hA : A.pcFree)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i →
      cr a = some i) :
    cpsBranchWithin 2 (hdr + 32) cr
      ((regOwn .x5) ** (.x20 ↦ᵣ vOffset) ** A)
      (hdr + 36 + signExtend13 (-40 : BitVec 13))
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset ≠ (136 : Word)⌝) ** A)
      (hdr + 40)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset = (136 : Word)⌝) ** A) := by
  have hli := cpsTripleWithin_extend_code hmemLi
    (li_spec_gen_own_within .x5 (136 : Word) (hdr + 32) (by decide))
  rw [show (hdr + 32 : Word) + 4 = hdr + 36 by
    rw [BitVec.add_assoc, show ((32 : Word) + 4) = (36 : Word) from by decide]] at hli
  have hliF := cpsTripleWithin_frameR ((.x20 ↦ᵣ vOffset) ** A)
    (pcFree_sepConj (by pcf) hA) hli
  have hb := cpsBranchWithin_extend_code hmemBne
    (bne_spec_gen_within .x20 .x5 (-40 : BitVec 13) vOffset
      (136 : Word) (hdr + 36))
  have hbF := cpsBranchWithin_frameR A hA hb
  have hseq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hliF hbF
  rw [show (hdr + 36 : Word) + 4 = hdr + 40 by
    rw [BitVec.add_assoc, show ((36 : Word) + 4) = (40 : Word) from by decide]] at hseq
  exact hseq

private theorem segments_absorb_spec (cr : CodeReq) (hdr scratchBase v10 : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemMv : ∀ a i, CodeReq.singleton hdr (.MV .x10 .x19) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 4) (.CSRS 0x800 .x10) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 hdr (hdr + 8) cr
      ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      ((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A) := by
  have hmv := cpsTripleWithin_extend_code hmemMv
    (mv_spec_gen_within .x10 .x19 scratchBase v10 hdr (by decide))
  rw [show (hdr : Word) + 4 = hdr + 4 by rfl] at hmv
  have hmvF := cpsTripleWithin_frameR
    (regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
    (pcFree_sepConj (pcFree_regOwns _)
      (pcFree_sepConj (bytesRegion_pcFree _ _) hA)) hmv
  have hcsrs := csrs_keccak_x10_own_flat (hdr + 4) scratchBase st
    ((.x19 ↦ᵣ scratchBase) ** A)
    (pcFree_sepConj (by pcf) hA) hst hb8 hvalid
  rw [show (hdr + 4 : Word) + 4 = hdr + 8 by
    rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]] at hcsrs
  have hcsrs' := cpsTripleWithin_extend_code hmemCsrs hcsrs
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmvF hcsrs'
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hseq

private theorem segments_rate_continuation_spec
    (cr : CodeReq) (hdr scratchBase v10 : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i →
      cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i →
      cr a = some i) :
    cpsTripleWithin 4 (hdr + 40) (hdr - 4) cr
      ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st **
        (.x20 ↦ᵣ (136 : Word)) ** A)
      ((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        (.x20 ↦ᵣ (0 : Word)) ** A) := by
  have hmemCsrs' : ∀ a i,
      CodeReq.singleton ((hdr + 40) + 4) (.CSRS 0x800 .x10) a = some i →
        cr a = some i := by
    intro a i h
    rw [show (hdr + 40 : Word) + 4 = hdr + 44 by
      rw [BitVec.add_assoc, show ((40 : Word) + 4) = (44 : Word) from by decide]] at h
    exact hmemCsrs a i h
  have hAbs := segments_absorb_spec cr (hdr + 40) scratchBase v10 st
    ((.x20 ↦ᵣ (136 : Word)) ** A)
    (pcFree_sepConj (by pcf) hA) hst hb8 hvalid hmemMv hmemCsrs'
  rw [show (hdr + 40 : Word) + 8 = hdr + 48 by
    rw [BitVec.add_assoc, show ((40 : Word) + 8) = (48 : Word) from by decide]] at hAbs
  have hLi := cpsTripleWithin_extend_code hmemLi
    (li_spec_gen_within .x20 (136 : Word) (0 : Word) (hdr + 48) (by decide))
  rw [show (hdr + 48 : Word) + 4 = hdr + 52 by
    rw [BitVec.add_assoc, show ((48 : Word) + 4) = (52 : Word) from by decide]] at hLi
  let T : Assertion :=
    (.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
      regOwns keccakCsrsRest **
      bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) ** A
  have hT : T.pcFree := by
    simp only [T]
    exact pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf)
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj (bytesRegion_pcFree _ _) hA)))
  have hLiF := cpsTripleWithin_frameR T hT hLi
  let Pzero : Assertion := (.x20 ↦ᵣ (0 : Word)) ** T
  have hPzero : Pzero.pcFree := by
    simp only [Pzero]
    exact pcFree_sepConj (by pcf) hT
  have hJal0 := jal0_spec_pcFree (-56 : BitVec 21) (hdr + 52) (P := Pzero) hPzero
  have hJal := cpsTripleWithin_extend_code hmemJal hJal0
  rw [show (hdr + 52 : Word) + signExtend21 (-56 : BitVec 21) = hdr - 4 by
    rw [show signExtend21 (-56 : BitVec 21) = (-56 : Word) from by decide]
    bv_omega] at hJal
  have hTail := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hLiF hJal
  have hAll := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [T] at hp ⊢; xperm_hyp hp) hAbs hTail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by simp only [Pzero, T] at hq ⊢; xperm_hyp hq) hAll

private theorem segments_rate_branch_spec
    (cr : CodeReq) (hdr scratchBase v10 vOffset : Word)
    (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hb8 : scratchBase.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i →
      cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i →
      cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i →
      cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i →
      cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i →
      cr a = some i) :
    cpsBranchWithin 6 (hdr + 32) cr
      ((regOwn .x5) ** (.x20 ↦ᵣ vOffset) ** (.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A)
      (hdr - 4)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset ≠ (136 : Word)⌝) **
          ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
            regOwns keccakCsrsRest ** bytesRegion scratchBase st ** A))
      (hdr - 4)
        (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
          (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
          (⌜vOffset = (136 : Word)⌝ ** A)) := by
  let Arate : Assertion :=
    (.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
      bytesRegion scratchBase st ** A
  have hArate : Arate.pcFree := by
    simp only [Arate]
    exact pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf)
        (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj (bytesRegion_pcFree _ _) hA)))
  have hRate := segments_rate_test_spec cr hdr vOffset Arate hArate hmemLi hmemBne
  have hRate' : cpsBranchWithin 2 (hdr + 32) cr
      ((regOwn .x5) ** (.x20 ↦ᵣ vOffset) ** Arate)
      (hdr - 4)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset ≠ (136 : Word)⌝) ** Arate)
      (hdr + 40)
        (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
          ⌜vOffset = (136 : Word)⌝) ** Arate) := by
    simpa only [Arate, show (hdr + 36 : Word) + signExtend13 (-40 : BitVec 13) = hdr - 4 by
      rw [show signExtend13 (-40 : BitVec 13) = (-40 : Word) from by decide]
      bv_omega] using hRate
  have hCont := segments_rate_continuation_spec cr hdr scratchBase v10 st
    ((.x5 ↦ᵣ (136 : Word)) ** (⌜vOffset = (136 : Word)⌝ ** A))
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA))
    hst hb8 hvalid hmemMv hmemCsrs hmemLi0 hmemJal
  have hCont' : cpsTripleWithin 4 (hdr + 40) (hdr - 4) cr
      (((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase st ** (.x20 ↦ᵣ (136 : Word)) **
        (.x5 ↦ᵣ (136 : Word))) ** (⌜vOffset = (136 : Word)⌝ ** A))
      (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
        regOwns keccakCsrsRest **
        bytesRegion scratchBase (setBytes st 0 (keccakBytes st 0)) **
        (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
        (⌜vOffset = (136 : Word)⌝ ** A)) := by
    simpa only [sepConj_assoc'] using hCont
  have hperm : ∀ h,
      (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) **
        ⌜vOffset = (136 : Word)⌝) ** Arate) h →
      (((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
        bytesRegion scratchBase st ** (.x20 ↦ᵣ (136 : Word)) **
        (.x5 ↦ᵣ (136 : Word))) ** (⌜vOffset = (136 : Word)⌝ ** A)) h := by
    intro h hp
    have hp' :
        ((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) ** Arate **
          ⌜vOffset = (136 : Word)⌝) h := by
      simpa only [Arate] using (by
        have := hp
        xperm_hyp this)
    have heq : vOffset = (136 : Word) := by
      have hp'''' :
          (((.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) ** Arate) **
            ⌜vOffset = (136 : Word)⌝) h := by
        xperm_hyp hp'
      have hinner := (sepConj_pure_right (P :=
        (.x20 ↦ᵣ vOffset) ** (.x5 ↦ᵣ (136 : Word)) ** Arate) h).1 hp''''
      exact hinner.2
    have hp''' :
        ((.x20 ↦ᵣ (136 : Word)) ** (.x5 ↦ᵣ (136 : Word)) ** Arate **
          ⌜vOffset = (136 : Word)⌝) h := by
      simpa only [heq] using hp'
    have hp'''' :
        ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
          bytesRegion scratchBase st ** (.x20 ↦ᵣ (136 : Word)) **
          (.x5 ↦ᵣ (136 : Word)) ** ⌜vOffset = (136 : Word)⌝ ** A) h := by
      simp only [Arate] at hp''' ⊢
      xperm_hyp hp'''
    simpa only [sepConj_assoc'] using hp''''
  exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
    hRate' hperm hCont' (fun h hp => by
      simp only [Arate] at hp ⊢
      xperm_hyp hp)

private theorem segments_of_forall3 {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 r3 : Reg}
    (h : ∀ (v1 v2 v3 : Word),
      cpsTripleWithin nSteps entry exit_ cr
        (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2) ** (r3 ↦ᵣ v3)) Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (P ** (regOwn r1) ** (regOwn r2) ** (regOwn r3)) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hPP, hRb⟩ := hPR
  obtain ⟨h3, h4, hd2, hu2, hP3, hOwn⟩ := hPP
  obtain ⟨h5, h6, hd3, hu3, ⟨v1, hv1⟩, hOwn23⟩ := hOwn
  obtain ⟨h7, h8, hd4, hu4, ⟨v2, hv2⟩, ⟨v3, hv3⟩⟩ := hOwn23
  exact h v1 v2 v3 R hR s hcr
    ⟨hp, hcompat, h1, h2, hd, hu,
      ⟨h3, h4, hd2, hu2, hP3,
        ⟨h5, h6, hd3, hu3, hv1,
          ⟨h7, h8, hd4, hu4, hv2, hv3⟩⟩⟩, hRb⟩ hpc

private theorem segments_nonrate_boundary (off k : Nat) (hnext : off + k + 1 < 136) :
    BitVec.ofNat 64 (off + k + 1) ≠ (136 : Word) := by
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at hnat
  have h136 : BitVec.toNat (136 : Word) = 136 := by decide
  rw [h136] at hnat
  have hlt64 : off + k + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt64] at hnat
  omega

private theorem segments_byte_round_spec
    (cr : CodeReq) (hdr scratchBase inputBase : Word) (v10 : Word)
    (st inp : List (BitVec 8)) (off n k : Nat) (A : Assertion)
    (hA : A.pcFree) (hk : k < n) (hoff : off < 136)
    (hst : st.length = 200) (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i → cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i → cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i → cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i → cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i → cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i → cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i → cr a = some i)
    (hmem7 : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i → cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i → cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i → cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i → cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i → cr a = some i) :
    cpsBranchWithin 14 hdr cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (st) ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A)
      (hdr - 4) (fun h =>
        (((.x20 ↦ᵣ (BitVec.ofNat 64 (off + 1))) **
          (.x5 ↦ᵣ (136 : Word)) **
          ⌜BitVec.ofNat 64 (off + 1) ≠ (136 : Word)⌝) **
          ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
            regOwns keccakCsrsRest **
            bytesRegion scratchBase (segmentsByteStep st inp (off) k) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A)) h)
      (hdr - 4) (fun h =>
        (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase
            (setBytes (segmentsByteStep st inp (off) k) 0
              (keccakBytes (segmentsByteStep st inp (off) k) 0)) **
          (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
          ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 **
            (⌜BitVec.ofNat 64 (off + 1) = (136 : Word)⌝ ** A))) h) := by
  let F : Assertion := (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A
  have hF : F.pcFree := by
    simp only [F]
    exact pcFree_sepConj (by pcf) (pcFree_sepConj (pcFree_regOwns _) hA)
  have hbodyVals : ∀ v5 v6 v7,
      cpsTripleWithin 8 hdr (hdr + 32) cr
        ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
          bytesRegion scratchBase (st) ** bytesRegion inputBase inp **
          F ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7))
        ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + 1))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion scratchBase (segmentsByteStep st inp (off) k) **
          bytesRegion inputBase inp ** F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) := by
    intro v5 v6 v7
    have h := segments_byte_body_step cr hdr scratchBase inputBase st inp off n k
      v5 v6 v7 hk hoff hst hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI
      hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6 hmem7
    have hF' := cpsTripleWithin_frameR F hF h
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF'
  have hbody : cpsTripleWithin 8 hdr (hdr + 32) cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (st) ** bytesRegion inputBase inp **
        F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + 1))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
        bytesRegion scratchBase (segmentsByteStep st inp (off) k) **
        bytesRegion inputBase inp ** F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7) := by
    refine cpsTripleWithin_weaken
      (fun _ hp => by
        simp only [F] at hp ⊢
        xperm_hyp hp)
      (fun _ hq => by
        simp only [F] at hq ⊢
        xperm_hyp hq)
      (segments_of_forall3
      (P :=
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
          bytesRegion scratchBase (st) **
          bytesRegion inputBase inp ** F)
      (Q :=
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + 1))) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion scratchBase (segmentsByteStep st inp (off) k) **
          bytesRegion inputBase inp ** F ** regOwn .x5 ** regOwn .x6 ** regOwn .x7)
      (r1 := .x5) (r2 := .x6) (r3 := .x7)
      (fun v5 v6 v7 => by
        refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => hq)
          (hbodyVals v5 v6 v7)
        simp only [F] at hp ⊢
        xperm_hyp hp))
  let A0 : Assertion :=
    (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
      bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A
  have hA0 : A0.pcFree := by
    simp only [A0]
    exact pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf)
      (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA))))
  have hRate := segments_rate_branch_spec cr hdr scratchBase v10
    (BitVec.ofNat 64 (off + 1))
    (segmentsByteStep st inp (off) k) A0 hA0
    (by simp [segmentsByteStep, hst]) hb8s hvalid hmemLi hmemBne
    hmemMv hmemCsrs hmemLi0 hmemJal
  have hSeq := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by simp only [F, A0] at hp ⊢; xperm_hyp hp) hbody hRate
  exact cpsBranchWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by
      simp only [A0] at hq ⊢
      xperm_hyp hq)
    (fun _ hq => by
      simp only [A0] at hq ⊢
      xperm_hyp hq) hSeq

private theorem segments_byte_round_nonrate_spec
    (cr : CodeReq) (hdr scratchBase inputBase : Word) (v10 : Word)
    (st0 inp : List (BitVec 8)) (off n k : Nat) (A : Assertion)
    (hA : A.pcFree) (hk : k < n) (hnext : off + k + 1 < 136)
    (hst : st0.length = 200) (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off + k) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off + k)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i → cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i → cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i → cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i → cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i → cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i → cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i → cr a = some i)
    (hmem7 : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i → cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i → cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i → cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i → cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i → cr a = some i) :
    cpsTripleWithin 14 hdr (hdr - 4) cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A)
      (((.x20 ↦ᵣ (BitVec.ofNat 64 (off + k + 1))) **
          (.x5 ↦ᵣ (136 : Word)) **
          ⌜BitVec.ofNat 64 (off + k + 1) ≠ (136 : Word)⌝) **
        ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase (xorBytesAt st0 inp off (k + 1)) **
          (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A)) := by
  have hround := segments_byte_round_spec cr hdr scratchBase inputBase v10
    (xorBytesAt st0 inp off k) inp (off + k) n k A
    hA hk (by omega) (by rw [xorBytesAt_length, hst]) hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI hvalid
    hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6 hmem7 hmemLi hmemBne hmemMv hmemCsrs
    hmemLi0 hmemJal
  have hkState : off + k < (xorBytesAt st0 inp off k).length := by
    rw [xorBytesAt_length, hst]
    omega
  have hstep := segmentsByteStep_xorBytesAt_succ st0 inp off k hkState
    (Nat.lt_of_lt_of_le hk hinp)
  rw [hstep] at hround
  apply cpsBranchWithin_takenPath hround
  intro hp hq
  extract_pure_deep hq
  obtain ⟨heq, _⟩ := hq
  exact segments_nonrate_boundary off k hnext heq

private theorem segments_byte_round_rate_spec
    (cr : CodeReq) (hdr scratchBase inputBase : Word) (v10 : Word)
    (st0 inp : List (BitVec 8)) (off n k : Nat) (A : Assertion)
    (hA : A.pcFree) (hk : k < n) (hoff : off + k < 136)
    (hrate : off + k + 1 = 136)
    (hst : st0.length = 200) (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + (off + k) < 2 ^ 64)
    (hbaseI : inputBase.toNat + k < 2 ^ 64)
    (hvalidS : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (off + k)) = true)
    (hvalidI : isValidByteAccess
      (inputBase + BitVec.ofNat 64 k) = true)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hmem0 : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x21 0) a = some i → cr a = some i)
    (hmem1 : ∀ a i, CodeReq.singleton (hdr + 4) (.ADD .x6 .x19 .x20) a = some i → cr a = some i)
    (hmem2 : ∀ a i, CodeReq.singleton (hdr + 8) (.LBU .x7 .x6 0) a = some i → cr a = some i)
    (hmem3 : ∀ a i, CodeReq.singleton (hdr + 12) (.XOR .x7 .x7 .x5) a = some i → cr a = some i)
    (hmem4 : ∀ a i, CodeReq.singleton (hdr + 16) (.SB .x6 .x7 0) a = some i → cr a = some i)
    (hmem5 : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x21 .x21 1) a = some i → cr a = some i)
    (hmem6 : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x22 .x22 (-1)) a = some i → cr a = some i)
    (hmem7 : ∀ a i, CodeReq.singleton (hdr + 28) (.ADDI .x20 .x20 1) a = some i → cr a = some i)
    (hmemLi : ∀ a i, CodeReq.singleton (hdr + 32) (.LI .x5 (136 : Word)) a = some i → cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 36) (.BNE .x20 .x5 (-40)) a = some i → cr a = some i)
    (hmemMv : ∀ a i, CodeReq.singleton (hdr + 40) (.MV .x10 .x19) a = some i → cr a = some i)
    (hmemCsrs : ∀ a i, CodeReq.singleton (hdr + 44) (.CSRS 0x800 .x10) a = some i → cr a = some i)
    (hmemLi0 : ∀ a i, CodeReq.singleton (hdr + 48) (.LI .x20 (0 : Word)) a = some i → cr a = some i)
    (hmemJal : ∀ a i, CodeReq.singleton (hdr + 52) (.JAL .x0 (-56)) a = some i → cr a = some i) :
    cpsTripleWithin 14 hdr (hdr - 4) cr
      ((.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 (off + k))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x22 ↦ᵣ (BitVec.ofNat 64 (n - k))) **
        bytesRegion scratchBase (xorBytesAt st0 inp off k) ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
        (.x10 ↦ᵣ v10) ** regOwns keccakCsrsRest ** A)
      (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
          regOwns keccakCsrsRest **
          bytesRegion scratchBase
            (setBytes (xorBytesAt st0 inp off (k + 1)) 0
              (keccakBytes (xorBytesAt st0 inp off (k + 1)) 0)) **
          (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
        ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
          (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
          bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 **
          (⌜BitVec.ofNat 64 (off + k + 1) = (136 : Word)⌝ ** A))) := by
  have hround := segments_byte_round_spec cr hdr scratchBase inputBase v10
    (xorBytesAt st0 inp off k) inp (off + k) n k A
    hA hk hoff (by rw [xorBytesAt_length, hst]) hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI hvalid
    hmem0 hmem1 hmem2 hmem3 hmem4 hmem5 hmem6 hmem7 hmemLi hmemBne hmemMv hmemCsrs
    hmemLi0 hmemJal
  have hkState : off + k < (xorBytesAt st0 inp off k).length := by
    rw [xorBytesAt_length, hst]
    omega
  have hstep := segmentsByteStep_xorBytesAt_succ st0 inp off k hkState
    (Nat.lt_of_lt_of_le hk hinp)
  rw [hstep] at hround
  apply cpsBranchWithin_ntakenPath hround
  intro hp hq
  extract_pure_deep hq
  obtain ⟨hne, _⟩ := hq
  apply hne
  rw [hrate]
  rfl

private theorem segmentsFillAfter_step (off q : Nat) :
    segmentsFillAfter off (q + 1) =
      let fill := segmentsFillAfter off q
      if fill + 1 = 136 then 0 else fill + 1 := by
  induction q generalizing off with
  | zero => rfl
  | succ q ih =>
      simpa [segmentsFillAfter] using
        ih (if off + 1 = 136 then 0 else off + 1)

private theorem segmentsStateFold_length (st inp : List (BitVec 8))
    (off cursor q : Nat) :
    (segmentsStateFold st inp off cursor q).length = st.length := by
  induction q generalizing st off cursor with
  | zero => rfl
  | succ q ih =>
      simp only [segmentsStateFold]
      split
      · rw [ih]
        simp [segmentsByteStep]
      · rw [ih]
        simp [segmentsByteStep]

private theorem segments_two_values_to_owns {P Q : Assertion} {v5 v10 : Word} :
    ∀ h, (P ** ((.x5 ↦ᵣ v5) ** ((.x10 ↦ᵣ v10) ** Q))) h →
      (P ** (regOwn .x5 ** (regOwn .x10 ** Q))) h := by
  intro h hp
  exact sepConj_mono_right
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono_left (regIs_implies_regOwn .x10))) h hp

private theorem segments_byte_loop_spec
    (scratchBase inputBase : Word) (st inp : List (BitVec 8))
    (off n : Nat) (A : Assertion) (hA : A.pcFree)
    (hoff : off < 136) (hst : st.length = 200) (hinp : n ≤ inp.length)
    (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + 135 < 2 ^ 64)
    (hbaseI : ∀ j, j < n → inputBase.toNat + j < 2 ^ 64)
    (hvalidS : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hvalidI : ∀ j, j < n →
      isValidByteAccess (inputBase + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (n * 15 + 1) (B + 104) (B + 84) segmentsCr
      ((.x22 ↦ᵣ (BitVec.ofNat 64 n)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (BitVec.ofNat 64 off)) **
        (.x21 ↦ᵣ inputBase) **
        bytesRegion scratchBase st ** bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwns keccakCsrsRest ** A)
      ((.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (BitVec.ofNat 64 (segmentsFillAfter off n))) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 n)) **
        bytesRegion scratchBase (segmentsStateFold st inp off 0 n) **
        bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwns keccakCsrsRest ** A) := by
  let invBase : Nat → Assertion := fun rem =>
    (.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ (BitVec.ofNat 64 (segmentsFillAfter off (n - rem)))) **
      (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (n - rem))) **
      bytesRegion scratchBase (segmentsStateFold st inp off 0 (n - rem)) **
      bytesRegion inputBase inp **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
      regOwns keccakCsrsRest ** A
  let inv : Nat → Assertion := fun rem => regOwn .x10 ** invBase rem
  have hinv : ∀ rem, (inv rem).pcFree := by
    intro rem
    simp only [inv, invBase]
    pcf; assumption
  have hbody : ∀ rem, rem < n →
      cpsTripleWithin 14 (B + 108) (B + 104) segmentsCr
        ((.x22 ↦ᵣ (BitVec.ofNat 64 (rem + 1))) **
          (.x0 ↦ᵣ (0 : Word)) ** inv (rem + 1))
        ((.x22 ↦ᵣ (BitVec.ofNat 64 rem)) **
          (.x0 ↦ᵣ (0 : Word)) ** inv rem) := by
    intro rem hrem
    let k := n - (rem + 1)
    let stq := segmentsStateFold st inp off 0 k
    let fill := segmentsFillAfter off k
    have hk : k < n := by
      dsimp [k]
      omega
    have hk1 : k + 1 = n - rem := by
      dsimp [k]
      omega
    have hsub : n - (n - (rem + 1)) = rem + 1 := by omega
    have hremEq : n - (k + 1) = rem := by
      dsimp [k]
      omega
    have hfill : fill < 136 := by
      exact segmentsFillAfter_lt off k hoff
    have hfillStep : segmentsFillAfter off (k + 1) =
        if fill + 1 = 136 then 0 else fill + 1 := by
      simpa [fill] using segmentsFillAfter_step off k
    have hstq : stq.length = 200 := by
      dsimp [stq]
      rw [segmentsStateFold_length, hst]
    have hbaseSq : scratchBase.toNat + fill < 2 ^ 64 := by
      dsimp [fill]
      have : segmentsFillAfter off k < 136 := segmentsFillAfter_lt off k hoff
      omega
    have hbaseIq : inputBase.toNat + k < 2 ^ 64 := by
      exact hbaseI k hk
    have hvalidSq : isValidByteAccess
        (scratchBase + BitVec.ofNat 64 fill) = true := by
      simpa [isValidByteAccess] using hvalidS fill (by omega)
    have hvalidIq : isValidByteAccess
        (inputBase + BitVec.ofNat 64 k) = true := hvalidI k hk
    have hbodyVal : ∀ v10 : Word,
        cpsTripleWithin 14 (B + 108) (B + 104) segmentsCr
          (((.x22 ↦ᵣ (BitVec.ofNat 64 (rem + 1))) ** invBase (rem + 1)) **
            (.x10 ↦ᵣ v10))
          (((.x22 ↦ᵣ (BitVec.ofNat 64 rem)) ** invBase rem) ** regOwn .x10) := by
      intro v10
      have hround0 := segments_byte_round_spec
        segmentsCr (B + 108) scratchBase inputBase v10 stq inp fill n k A hA hk hfill
        hstq hinp hn64 hb8s hb8i hbaseSq hbaseIq hvalidSq hvalidIq hvalidS
        (segments_mem_at 27 (.LBU .x5 .x21 0) (B + 108) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 28 (.ADD .x6 .x19 .x20) (B + 112) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 29 (.LBU .x7 .x6 0) (B + 116) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 30 (.XOR .x7 .x7 .x5) (B + 120) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 31 (.SB .x6 .x7 0) (B + 124) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 32 (.ADDI .x21 .x21 1) (B + 128) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 33 (.ADDI .x22 .x22 (-1)) (B + 132) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 34 (.ADDI .x20 .x20 1) (B + 136) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 35 (.LI .x5 (136 : Word)) (B + 140) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 36 (.BNE .x20 .x5 (-40)) (B + 144) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 37 (.MV .x10 .x19) (B + 148) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 38 (.CSRS 0x800 .x10) (B + 152) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 39 (.LI .x20 (0 : Word)) (B + 156) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
        (segments_mem_at 40 (.JAL .x0 (-56)) (B + 160) (by decide)
          (by rw [segmentsProgL_len]; decide) (by rfl))
      let Ppre : Assertion :=
        ((.x22 ↦ᵣ (BitVec.ofNat 64 (rem + 1))) ** invBase (rem + 1)) **
          (.x10 ↦ᵣ v10)
      let Qn : Assertion :=
        (((.x20 ↦ᵣ (BitVec.ofNat 64 (fill + 1))) **
            (.x5 ↦ᵣ (136 : Word)) **
            ⌜BitVec.ofNat 64 (fill + 1) ≠ (136 : Word)⌝) **
          ((.x10 ↦ᵣ v10) ** (.x19 ↦ᵣ scratchBase) **
            regOwns keccakCsrsRest **
            bytesRegion scratchBase (segmentsByteStep stq inp fill k) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 ** A))
      let Qr : Assertion :=
        (((.x10 ↦ᵣ scratchBase) ** (.x19 ↦ᵣ scratchBase) **
            regOwns keccakCsrsRest **
            bytesRegion scratchBase
              (setBytes (segmentsByteStep stq inp fill k) 0
                (keccakBytes (segmentsByteStep stq inp fill k) 0)) **
            (.x20 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ (136 : Word))) **
          ((.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7 **
            (⌜BitVec.ofNat 64 (fill + 1) = (136 : Word)⌝ ** A)))
      have hroundP : cpsBranchWithin 14 (B + 108) segmentsCr Ppre
          (B + 104) Qn (B + 104) Qr := by
        refine cpsBranchWithin_weaken
          (fun _ hp => by
            simp only [Ppre, invBase, k, stq, fill] at hp ⊢
            rw [hsub]
            xperm_hyp hp)
          (fun _ hq => by simpa [Qn] using hq)
          (fun _ hq => by simpa [Qr] using hq) hround0
      by_cases hrate : fill + 1 = 136
      · have hpath := cpsBranchWithin_ntakenPath hroundP (fun _ hq => by
          simp only [Qn] at hq
          extract_pure_deep hq
          obtain ⟨hne, _⟩ := hq
          apply hne
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_ofNat, hrate])
        refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hpath
        simp only [Qr] at hq
        extract_pure_deep hq
        obtain ⟨heq, hrest⟩ := hq
        have hfold : segmentsStateFold st inp off 0 (k + 1) =
            setBytes (segmentsByteStep stq inp fill k) 0
              (keccakBytes (segmentsByteStep stq inp fill k) 0) := by
          rw [segmentsStateFold_step]
          simp only [Nat.zero_add]
          simp only [stq, fill, hrate, ↓reduceIte]
        have hfill' : segmentsFillAfter off (k + 1) = 0 := by
          rw [hfillStep]
          simp [hrate]
        have hrest' :
            (((.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
              bytesRegion scratchBase
                (setBytes (segmentsByteStep stq inp fill k) 0
                  (keccakBytes (segmentsByteStep stq inp fill k) 0)) **
              (.x20 ↦ᵣ (0 : Word)) **
              (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
              (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
              bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7) **
            ((.x5 ↦ᵣ (136 : Word)) ** ((.x10 ↦ᵣ scratchBase) ** A))) h := by
          sep_perm hrest
        have hown := segments_two_values_to_owns
          (P := (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
            bytesRegion scratchBase
              (setBytes (segmentsByteStep stq inp fill k) 0
                (keccakBytes (segmentsByteStep stq inp fill k) 0)) **
            (.x20 ↦ᵣ (0 : Word)) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7)
          (Q := A) (v5 := (136 : Word)) (v10 := scratchBase) h hrest'
        have hfold' : segmentsStateFold st inp off 0 (k + 1) =
            segmentsStateFold st inp off 0 (n - rem) := by
          rw [← hk1]
        have hrem' : n - (k + 1) = rem := hremEq
        rw [hrem'] at hown
        rw [hk1] at hown
        rw [← hfold] at hown
        rw [hfold'] at hown
        have hfillTarget : segmentsFillAfter off (n - rem) = 0 := by
          rw [← hk1, hfillStep]
          simp [hrate]
        simp only [invBase] at ⊢
        rw [hfillTarget]
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) by decide]
        xperm_hyp hown
      · have hpath := cpsBranchWithin_takenPath hroundP (fun _ hq => by
          simp only [Qr] at hq
          extract_pure_deep hq
          obtain ⟨heq, _⟩ := hq
          exact hrate (by
            have := congrArg BitVec.toNat heq
            have hlt : fill + 1 < 2 ^ 64 := by omega
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
            have h136 : BitVec.toNat (136 : Word) = 136 := by decide
            rw [h136] at this
            exact this))
        refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hpath
        simp only [Qn] at hq
        extract_pure_deep hq
        obtain ⟨hne, hrest⟩ := hq
        have hfold : segmentsStateFold st inp off 0 (k + 1) =
            segmentsByteStep stq inp fill k := by
          rw [segmentsStateFold_step]
          simp only [Nat.zero_add]
          simp only [stq, fill, hrate, ↓reduceIte]
        have hfill' : segmentsFillAfter off (k + 1) = fill + 1 := by
          rw [hfillStep]
          simp [hrate]
        have hrest' :
            (((.x20 ↦ᵣ (BitVec.ofNat 64 (fill + 1))) **
              (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
              bytesRegion scratchBase (segmentsByteStep stq inp fill k) **
              (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
              (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
              bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7) **
            ((.x5 ↦ᵣ (136 : Word)) ** ((.x10 ↦ᵣ v10) ** A))) h := by
          sep_perm hrest
        have hown := segments_two_values_to_owns
          (P := (.x20 ↦ᵣ (BitVec.ofNat 64 (fill + 1))) **
            (.x19 ↦ᵣ scratchBase) ** regOwns keccakCsrsRest **
            bytesRegion scratchBase (segmentsByteStep stq inp fill k) **
            (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
            (.x22 ↦ᵣ (BitVec.ofNat 64 (n - (k + 1)))) **
            bytesRegion inputBase inp ** regOwn .x6 ** regOwn .x7)
          (Q := A) (v5 := (136 : Word)) (v10 := v10) h hrest'
        have hfold' : segmentsStateFold st inp off 0 (k + 1) =
            segmentsStateFold st inp off 0 (n - rem) := by
          rw [← hk1]
        have hrem' : n - (k + 1) = rem := hremEq
        rw [hrem'] at hown
        rw [hk1] at hown
        rw [← hfold] at hown
        rw [hfold'] at hown
        have hfillTarget : segmentsFillAfter off (n - rem) = fill + 1 := by
          rw [← hk1, hfillStep]
          simp [hrate]
        simp only [invBase] at ⊢
        rw [hfillTarget]
        xperm_hyp hown
    have hbodyOwn0 := cpsTripleWithin_of_forall_regIs_to_regOwn
      (r := .x10)
      (P := (.x22 ↦ᵣ (BitVec.ofNat 64 (rem + 1))) **
        invBase (rem + 1))
      (h := fun v => by
        exact hbodyVal v)
    have hbodyOwn := cpsTripleWithin_frameR
      (.x0 ↦ᵣ (0 : Word)) (by pcf) hbodyOwn0
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hbodyOwn
  have hloop := countdownLoop_spec
    (cr := segmentsCr) (hdr := B + 104) (exitAddr := B + 84)
    (ctr := .x22) (exitOff := (-20 : BitVec 13)) (bodyStep := 14) (N := n)
    (inv := inv) (_hctr_ne := by decide) (hNbound := hn64)
    (hexit := by decide) (hpcFree := hinv)
    (hguardMem := segments_mem_at 26 (.BEQ .x22 .x0 (-20 : BitVec 13))
      (B + 104) (by decide) (by rw [segmentsProgL_len]; decide) (by rfl))
    (hbody := hbody)
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hloop
  · simp only [inv, invBase, Nat.sub_self, segmentsFillAfter, segmentsStateFold]
    simp only [BitVec.add_zero]
    xperm_hyp hp
  · simp only [inv, invBase] at hq
    rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) by decide] at hq
    rw [Nat.sub_zero] at hq
    xperm_hyp hq

/-! ## Descriptor fetch and cross-rate composition

The outer loop loads one `(ptr,len)` pair before entering the byte loop.  The
fetch theorem below keeps the table cell as a separate read-only region, so
the following composition can frame the remaining descriptor cells and all
payload regions without making the byte loop depend on table layout details.
-/

private def segmentsDescriptorBytes (p : Word) (n : Nat) : List (BitVec 8) :=
  dwordBytes p ++ dwordBytes (BitVec.ofNat 64 n)

private theorem segmentsDescriptorBytes_length (p : Word) (n : Nat) :
    (segmentsDescriptorBytes p n).length = 16 := by
  simp only [segmentsDescriptorBytes, length_dwordBytes, List.length_append]

private theorem segmentsDescriptorBytes_first (p : Word) (n : Nat) :
    packBytes ((segmentsDescriptorBytes p n).drop 0 |>.take 8) = p := by
  simp only [segmentsDescriptorBytes, List.drop_zero]
  rw [take8_dword_append p (dwordBytes (BitVec.ofNat 64 n)),
    packBytes_dwordBytes]

private theorem segmentsDescriptorBytes_second (p : Word) (n : Nat) :
    packBytes ((segmentsDescriptorBytes p n).drop 8 |>.take 8) =
      BitVec.ofNat 64 n := by
  simp only [segmentsDescriptorBytes]
  rw [show (dwordBytes p ++ dwordBytes (BitVec.ofNat 64 n)).drop 8 =
      dwordBytes (BitVec.ofNat 64 n) by
        rw [List.drop_append_of_le_length (by simp)]
        simp [length_dwordBytes]]
  have htake : (dwordBytes (BitVec.ofNat 64 n)).take 8 =
      dwordBytes (BitVec.ofNat 64 n) := by
    exact List.take_of_length_le (by rw [length_dwordBytes])
  rw [htake, packBytes_dwordBytes]

private theorem segments_descriptor_counter_decrement (n : Nat)
    (_hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) =
      BitVec.ofNat 64 n := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

private theorem segments_descriptor_fetch_spec
    (tableBase p : Word) (n m : Nat) (v21 v22 : Word) (A : Assertion)
    (hA : A.pcFree) (hm : m + 1 < 2 ^ 64)
    (hmem0 : ∀ a i,
      CodeReq.singleton (B + 88) (.LD .x21 .x8 0) a = some i →
        segmentsCr a = some i)
    (hmem1 : ∀ a i,
      CodeReq.singleton (B + 92) (.LD .x22 .x8 8) a = some i →
        segmentsCr a = some i)
    (hmem2 : ∀ a i,
      CodeReq.singleton (B + 96) (.ADDI .x8 .x8 (16 : BitVec 12)) a = some i →
        segmentsCr a = some i)
    (hmem3 : ∀ a i,
      CodeReq.singleton (B + 100) (.ADDI .x9 .x9 (-1 : BitVec 12)) a = some i →
        segmentsCr a = some i) :
    cpsTripleWithin 4 (B + 88) (B + 104) segmentsCr
      ((.x8 ↦ᵣ tableBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
      ((.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 m) ** (.x21 ↦ᵣ p) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A) := by
  have hld0 := bytesRegion_ld_within .x21 .x8 tableBase v21 (B + 88)
    (segmentsDescriptorBytes p n) 0 (by decide)
    (by simp [segmentsDescriptorBytes])
    (by decide)
  rw [segmentsDescriptorBytes_first] at hld0
  have hld0' := cpsTripleWithin_extend_code hmem0 hld0
  rw [show (B + 88 : Word) + 4 = B + 92 by decide] at hld0'
  have hld0F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) ** (.x22 ↦ᵣ v22) ** A)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA)) hld0'
  have c0 : cpsTripleWithin 1 (B + 88) (B + 92) segmentsCr
      ((.x8 ↦ᵣ tableBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
      ((.x8 ↦ᵣ tableBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) **
        (.x21 ↦ᵣ p) ** (.x22 ↦ᵣ v22) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hld0F
  have hld1 := bytesRegion_ld_within .x22 .x8 tableBase v22 (B + 92)
    (segmentsDescriptorBytes p n) 1 (by decide)
    (by simp [segmentsDescriptorBytes])
    (by decide)
  rw [segmentsDescriptorBytes_second] at hld1
  have hld1' := cpsTripleWithin_extend_code hmem1 hld1
  rw [show (B + 92 : Word) + 4 = B + 96 by decide] at hld1'
  have hld1F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) ** (.x21 ↦ᵣ p) ** A)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hA)) hld1'
  have c1 : cpsTripleWithin 1 (B + 92) (B + 96) segmentsCr
      ((.x8 ↦ᵣ tableBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) **
        (.x21 ↦ᵣ p) ** (.x22 ↦ᵣ v22) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
      ((.x8 ↦ᵣ tableBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) **
        (.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hld1F
  have ha8 := addi_spec_gen_same_within .x8 tableBase
    (16 : BitVec 12) (B + 96) (by decide)
  have ha8' := cpsTripleWithin_extend_code hmem2 ha8
  rw [show (B + 96 : Word) + 4 = B + 100 by decide] at ha8'
  have hptr8 : tableBase + signExtend12 (16 : BitVec 12) =
      tableBase + BitVec.ofNat 64 16 := by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) by decide]
    exact congrArg (fun x : Word => tableBase + x) (by decide)
  rw [hptr8] at ha8'
  have ha8F := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) ** (.x21 ↦ᵣ p) **
      (.x22 ↦ᵣ BitVec.ofNat 64 n) **
      bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf) (pcFree_sepConj
        (bytesRegion_pcFree _ _) hA)))) ha8'
  have c2 : cpsTripleWithin 1 (B + 96) (B + 100) segmentsCr
      ((.x8 ↦ᵣ tableBase) ** (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) **
        (.x21 ↦ᵣ p) ** (.x22 ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
      ((.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) ** (.x21 ↦ᵣ p) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) ha8F
  have hac := addi_spec_gen_same_within .x9
    (BitVec.ofNat 64 (m + 1)) (-1 : BitVec 12) (B + 100) (by decide)
  have hac' := cpsTripleWithin_extend_code hmem3 hac
  rw [show (B + 100 : Word) + 4 = B + 104 by decide,
    segments_descriptor_counter_decrement m hm] at hac'
  have hacF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) ** (.x21 ↦ᵣ p) **
      (.x22 ↦ᵣ BitVec.ofNat 64 n) **
      bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf) (pcFree_sepConj
        (bytesRegion_pcFree _ _) hA)))) hac'
  have c3 : cpsTripleWithin 1 (B + 100) (B + 104) segmentsCr
      ((.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) ** (.x21 ↦ᵣ p) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A)
      ((.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) **
        (.x9 ↦ᵣ BitVec.ofNat 64 m) ** (.x21 ↦ᵣ p) **
        (.x22 ↦ᵣ BitVec.ofNat 64 n) **
        bytesRegion tableBase (segmentsDescriptorBytes p n) ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hacF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 c3))

/-! The descriptor counter's control shape is separate from the byte-state
    invariant.  A nonzero descriptor count takes the fall-through byte round
    and returns to the header; exhaustion takes the header branch to the next
    descriptor gate.  Keeping this combinator explicit prevents the eventual
    state invariant from silently changing the branch geometry. -/

private theorem segments_descriptor_loop_spec
    (cr : CodeReq) (hdr exitA : Word) (n : Nat)
    (inv : Nat → Assertion) (QA Q : Assertion)
    (hiterBranch : ∀ j, j < n →
      cpsBranchWithin 1 hdr cr (inv j) exitA QA (hdr + 4) (inv j))
    (hround : ∀ j, j < n →
      cpsTripleWithin 14 (hdr + 4) hdr cr (inv j) (inv (j + 1)))
    (hfinal : cpsTripleWithin 1 hdr exitA cr (inv n) Q) :
    cpsBranchWithin (n * 15 + 1) hdr cr (inv 0) exitA QA exitA Q := by
  apply twoExitRetLoop_spec n 15 1 inv
  · intro j hj
    exact cpsBranchWithin_seq_cpsTripleWithin_with_perm_same_cr
      (hiterBranch j hj)
      (fun _ hp => by xperm_hyp hp)
      (hround j hj)
      (fun _ hp => by xperm_hyp hp)
  · exact hfinal

private theorem segments_descriptor_header_spec
    (cr : CodeReq) (hdr exitA v : Word) (P : Assertion) (hP : P.pcFree)
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsBranchWithin 1 hdr cr
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      exitA (((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) ** ⌜v = (0 : Word)⌝)
      (hdr + 4) (((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) ** ⌜v ≠ (0 : Word)⌝) := by
  have hbr := cpsBranchWithin_extend_code hmem
    (beq_spec_gen_within .x22 .x0 (-20 : BitVec 13) v (0 : Word) hdr)
  rw [haddr] at hbr
  have hbrF := cpsBranchWithin_frameR P hP hbr
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    (fun _ hq => by xperm_hyp hq)
    hbrF

private theorem segments_descriptor_header_nonzero_spec
    (cr : CodeReq) (hdr exitA v : Word) (P QA : Assertion) (hP : P.pcFree)
    (hv : v ≠ (0 : Word))
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsBranchWithin 1 hdr cr
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      exitA QA
      (hdr + 4) ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hbr := segments_descriptor_header_spec cr hdr exitA v P hP haddr hmem
  exact cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun h hq => by
      have heq := ((sepConj_pure_right (P :=
        (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).2
      exact (hv heq).elim)
    (fun h hq => by
      exact ((sepConj_pure_right (P :=
        (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).1)
    hbr

private theorem segments_descriptor_header_zero_spec
    (cr : CodeReq) (hdr exitA v : Word) (P : Assertion) (hP : P.pcFree)
    (hv : v = (0 : Word))
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 hdr exitA cr
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      ((.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hbr := segments_descriptor_header_spec cr hdr exitA v P hP haddr hmem
  have htaken := cpsBranchWithin_takenPath hbr (fun h hq => by
    have hne := ((sepConj_pure_right (P :=
      (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).2
    exact hne hv)
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hq => ((sepConj_pure_right (P :=
      (.x22 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) h).1 hq).1)
    htaken

private theorem segments_descriptor_loop_with_header
    (cr : CodeReq) (hdr exitA : Word) (n : Nat)
    (payload : Nat → Assertion) (QA Q : Assertion)
    (hpayload : ∀ j, (payload j).pcFree)
    (hn64 : n < 2 ^ 64)
    (haddr : hdr + signExtend13 (-20 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x22 .x0 (-20 : BitVec 13)) a = some i →
      cr a = some i)
    (hround : ∀ j, j < n →
      cpsTripleWithin 14 (hdr + 4) hdr cr
        ((.x22 ↦ᵣ (BitVec.ofNat 64 (n - j))) ** (.x0 ↦ᵣ (0 : Word)) ** payload j)
        ((.x22 ↦ᵣ (BitVec.ofNat 64 (n - (j + 1)))) ** (.x0 ↦ᵣ (0 : Word)) **
          payload (j + 1)))
    (hfinal : cpsTripleWithin 1 hdr exitA cr
      ((.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) ** payload n) Q) :
    cpsBranchWithin (n * 15 + 1) hdr cr
      ((.x22 ↦ᵣ (BitVec.ofNat 64 n)) ** (.x0 ↦ᵣ (0 : Word)) ** payload 0)
      exitA QA exitA Q := by
  apply segments_descriptor_loop_spec cr hdr exitA n
    (fun j => (.x22 ↦ᵣ (BitVec.ofNat 64 (n - j))) **
      (.x0 ↦ᵣ (0 : Word)) ** payload j) QA Q
  · intro j hj
    have hne : BitVec.ofNat 64 (n - j) ≠ (0 : Word) := by
      intro heq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat] at hnat
      have hsub : n - j < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hsub] at hnat
      have hzero : BitVec.toNat (0 : Word) = 0 := by decide
      rw [hzero] at hnat
      omega
    simpa using segments_descriptor_header_nonzero_spec cr hdr exitA
      (BitVec.ofNat 64 (n - j)) (payload j) QA (hpayload j) hne haddr hmem
  · exact hround
  · simpa using hfinal

/-! The outer descriptor header is the same branch shape as the byte-loop
header, but it tests `s1` (`x9`) and jumps to the tail label after the final
descriptor.  Keeping this one-register variant explicit makes the subsequent
three-descriptor composition read as the actual control flow. -/

private theorem segments_outer_header_nonzero_spec
    (cr : CodeReq) (hdr exitA v : Word) (P QA : Assertion) (hP : P.pcFree)
    (hv : v ≠ (0 : Word))
    (haddr : hdr + signExtend13 (80 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x9 .x0 (80 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsBranchWithin 1 hdr cr
      ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      exitA QA
      (hdr + 4) ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hbr := cpsBranchWithin_extend_code hmem
    (beq_spec_gen_within .x9 .x0 (80 : BitVec 13) v (0 : Word) hdr)
  rw [haddr] at hbr
  have hbrF := cpsBranchWithin_frameR P hP hbr
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      have hq' : (((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜v = (0 : Word)⌝) ** P) h := by
        xperm_hyp hq
      have hq'' : (⌜v = (0 : Word)⌝ **
          ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)) h := by
        xperm_hyp hq'
      have heq := (sepConj_pure_left h).1 hq'' |>.1
      exact (hv heq).elim)
    (fun h hq => by
      have hq'' : (⌜v ≠ (0 : Word)⌝ **
          ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)) h := by
        xperm_hyp hq
      have hbase := (sepConj_pure_left h).1 hq'' |>.2
      xperm_hyp hbase)
    hbrF

private theorem segments_outer_header_nonzero_trip_spec
    (cr : CodeReq) (hdr exitA v : Word) (P : Assertion) (hP : P.pcFree)
    (hv : v ≠ (0 : Word))
    (haddr : hdr + signExtend13 (80 : BitVec 13) = exitA)
    (hmem : ∀ a i, CodeReq.singleton hdr (.BEQ .x9 .x0 (80 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)
      ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P) := by
  have hbr := cpsBranchWithin_extend_code hmem
    (beq_spec_gen_within .x9 .x0 (80 : BitVec 13) v (0 : Word) hdr)
  rw [haddr] at hbr
  have hbrF := cpsBranchWithin_frameR P hP hbr
  have hnt := cpsBranchWithin_ntakenPath hbrF (fun h hq => by
    have hq' : (((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜v = (0 : Word)⌝) ** P) h := by
      xperm_hyp hq
    have hq'' : (⌜v = (0 : Word)⌝ **
        ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)) h := by
      xperm_hyp hq'
    exact hv ((sepConj_pure_left h).1 hq'').1)
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun h hq => by
      have hq' : (((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜v ≠ (0 : Word)⌝) ** P) h := by
        xperm_hyp hq
      have hq'' : (⌜v ≠ (0 : Word)⌝ **
          ((.x9 ↦ᵣ v) ** (.x0 ↦ᵣ (0 : Word)) ** P)) h := by
        xperm_hyp hq'
      have hbase := (sepConj_pure_left h).1 hq'' |>.2
      xperm_hyp hbase)
    hnt

private theorem segments_outer_iteration_spec
    (scratchBase inputBase tableBase : Word) (st inp : List (BitVec 8))
    (off n m : Nat) (v21 v22 : Word) (A : Assertion) (hA : A.pcFree)
    (hm : m + 1 < 2 ^ 64) (hoff : off < 136) (hst : st.length = 200)
    (hinp : n ≤ inp.length) (hn64 : n < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0) (hb8i : inputBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + 135 < 2 ^ 64)
    (hbaseI : ∀ j, j < n → inputBase.toNat + j < 2 ^ 64)
    (hvalidS : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hvalidI : ∀ j, j < n →
      isValidByteAccess (inputBase + BitVec.ofNat 64 j) = true)
    (hhead : ∀ a i,
      CodeReq.singleton (B + 84) (.BEQ .x9 .x0 (80 : BitVec 13)) a = some i →
        segmentsCr a = some i)
    (hmem0 : ∀ a i,
      CodeReq.singleton (B + 88) (.LD .x21 .x8 0) a = some i →
        segmentsCr a = some i)
    (hmem1 : ∀ a i,
      CodeReq.singleton (B + 92) (.LD .x22 .x8 8) a = some i →
        segmentsCr a = some i)
    (hmem2 : ∀ a i,
      CodeReq.singleton (B + 96) (.ADDI .x8 .x8 (16 : BitVec 12)) a = some i →
        segmentsCr a = some i)
    (hmem3 : ∀ a i,
      CodeReq.singleton (B + 100) (.ADDI .x9 .x9 (-1 : BitVec 12)) a = some i →
        segmentsCr a = some i) :
    cpsTripleWithin (n * 15 + 6) (B + 84) (B + 84) segmentsCr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (m + 1)) ** (.x8 ↦ᵣ tableBase) **
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 off) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase st **
        bytesRegion tableBase (segmentsDescriptorBytes inputBase n) **
        bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwns keccakCsrsRest ** A)
      ((.x9 ↦ᵣ BitVec.ofNat 64 m) **
        (.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) **
        (.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ BitVec.ofNat 64 (segmentsFillAfter off n)) **
        (.x21 ↦ᵣ (inputBase + BitVec.ofNat 64 n)) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase (segmentsStateFold st inp off 0 n) **
        bytesRegion tableBase (segmentsDescriptorBytes inputBase n) **
        bytesRegion inputBase inp **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwns keccakCsrsRest ** A) := by
  let d : List (BitVec 8) := segmentsDescriptorBytes inputBase n
  let Pouter : Assertion :=
    (.x8 ↦ᵣ tableBase) ** (.x19 ↦ᵣ scratchBase) **
      (.x20 ↦ᵣ BitVec.ofNat 64 off) ** (.x21 ↦ᵣ v21) **
      (.x22 ↦ᵣ v22) ** bytesRegion scratchBase st **
      bytesRegion tableBase d ** bytesRegion inputBase inp **
      regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
      regOwns keccakCsrsRest ** A
  have hPouter : Pouter.pcFree := by
    simp only [Pouter]
    pcf; assumption
  have hhead' := segments_outer_header_nonzero_trip_spec segmentsCr
    (B + 84) (B + 164) (BitVec.ofNat 64 (m + 1)) Pouter hPouter
    (by
      intro heq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat] at hnat
      have hm64 : m + 1 < 2 ^ 64 := hm
      rw [Nat.mod_eq_of_lt hm64] at hnat
      have hz : BitVec.toNat (0 : Word) = 0 := by decide
      rw [hz] at hnat
      omega)
    (by decide) hhead
  let Afetch : Assertion :=
    (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ BitVec.ofNat 64 off) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion scratchBase st **
      bytesRegion inputBase inp ** regOwn .x5 ** regOwn .x6 **
      regOwn .x7 ** regOwn .x10 ** regOwns keccakCsrsRest ** A
  have hAfetch : Afetch.pcFree := by
    simp only [Afetch]
    pcf; assumption
  have hfetch := segments_descriptor_fetch_spec tableBase inputBase n m v21 v22
    Afetch hAfetch hm hmem0 hmem1 hmem2 hmem3
  let Abyte : Assertion :=
    (.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 16)) **
      (.x9 ↦ᵣ BitVec.ofNat 64 m) ** bytesRegion tableBase d ** A
  have hAbyte : Abyte.pcFree := by
    simp only [Abyte]
    pcf; assumption
  have hbyte := segments_byte_loop_spec scratchBase inputBase st inp off n Abyte
    hAbyte hoff hst hinp hn64 hb8s hb8i hbaseS hbaseI hvalidS hvalidI
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [Pouter, Afetch, d] at hp ⊢
      xperm_hyp hp)
    hhead' hfetch
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [Afetch, Abyte, d] at hp ⊢
      xperm_hyp hp)
    h01 hbyte
  have hsteps : 1 + 4 + (n * 15 + 1) = n * 15 + 6 := by omega
  rw [hsteps] at hall
  simp only [Pouter, Abyte, d] at hall ⊢
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    hall

/-! A concrete three-descriptor composition.  The theorem deliberately keeps
    three distinct payload regions and descriptor cells: the first iteration's
    post is therefore forced to feed the second iteration's fetch, and the
    second must expose the cross-rate state before the third can start. -/

private theorem segments_three_descriptor_spec
    (scratchBase tableBase p0 p1 p2 : Word)
    (st bs0 bs1 bs2 : List (BitVec 8)) (v21 v22 : Word)
    (A : Assertion) (hA : A.pcFree) (hst : st.length = 200)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hbaseS : scratchBase.toNat + 135 < 2 ^ 64)
    (hvalidS : ∀ j, j < 200 →
      isValidMemAddr (scratchBase + BitVec.ofNat 64 j) = true)
    (hb80 : p0.toNat % 8 = 0)
    (hb81 : p1.toNat % 8 = 0)
    (hb82 : p2.toNat % 8 = 0)
    (hbase0 : ∀ j, j < bs0.length → p0.toNat + j < 2 ^ 64)
    (hbase1 : ∀ j, j < bs1.length → p1.toNat + j < 2 ^ 64)
    (hbase2 : ∀ j, j < bs2.length → p2.toNat + j < 2 ^ 64)
    (hn0 : bs0.length < 2 ^ 64) (hn1 : bs1.length < 2 ^ 64)
    (hn2 : bs2.length < 2 ^ 64)
    (hvalid0 : ∀ j, j < bs0.length →
      isValidByteAccess (p0 + BitVec.ofNat 64 j) = true)
    (hvalid1 : ∀ j, j < bs1.length →
      isValidByteAccess (p1 + BitVec.ofNat 64 j) = true)
    (hvalid2 : ∀ j, j < bs2.length →
      isValidByteAccess (p2 + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin
        ((bs0.length * 15 + 6) + (bs1.length * 15 + 6) +
          (bs2.length * 15 + 6)) (B + 84) (B + 84) segmentsCr
      ((.x9 ↦ᵣ (3 : Word)) ** (.x8 ↦ᵣ tableBase) **
        (.x19 ↦ᵣ scratchBase) ** (.x20 ↦ᵣ (0 : Word)) **
        (.x21 ↦ᵣ v21) ** (.x22 ↦ᵣ v22) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase st **
        bytesRegion tableBase (segmentsDescriptorBytes p0 bs0.length) **
        bytesRegion (tableBase + BitVec.ofNat 64 16)
          (segmentsDescriptorBytes p1 bs1.length) **
        bytesRegion (tableBase + BitVec.ofNat 64 32)
          (segmentsDescriptorBytes p2 bs2.length) **
        bytesRegion p0 bs0 ** bytesRegion p1 bs1 ** bytesRegion p2 bs2 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwns keccakCsrsRest ** A)
      ((.x9 ↦ᵣ (0 : Word)) **
        (.x8 ↦ᵣ (tableBase + BitVec.ofNat 64 48)) **
        (.x19 ↦ᵣ scratchBase) **
        (.x20 ↦ᵣ (BitVec.ofNat 64
          (segmentsFillAfter
            (segmentsFillAfter
              (segmentsFillAfter 0 bs0.length) bs1.length) bs2.length))) **
        (.x21 ↦ᵣ (p2 + BitVec.ofNat 64 bs2.length)) **
        (.x22 ↦ᵣ (0 : Word)) ** (.x0 ↦ᵣ (0 : Word)) **
        bytesRegion scratchBase
          (segmentsStateFold
            (segmentsStateFold
              (segmentsStateFold st bs0 0 0 bs0.length)
              bs1 (segmentsFillAfter 0 bs0.length) 0 bs1.length)
            bs2
            (segmentsFillAfter
              (segmentsFillAfter 0 bs0.length) bs1.length) 0 bs2.length) **
        bytesRegion tableBase (segmentsDescriptorBytes p0 bs0.length) **
        bytesRegion (tableBase + BitVec.ofNat 64 16)
          (segmentsDescriptorBytes p1 bs1.length) **
        bytesRegion (tableBase + BitVec.ofNat 64 32)
          (segmentsDescriptorBytes p2 bs2.length) **
        bytesRegion p0 bs0 ** bytesRegion p1 bs1 ** bytesRegion p2 bs2 **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 **
        regOwns keccakCsrsRest ** A) := by
  have hhead : ∀ a i,
      CodeReq.singleton (B + 84) (.BEQ .x9 .x0 (80 : BitVec 13)) a = some i →
        segmentsCr a = some i :=
    segments_mem_at 21 (.BEQ .x9 .x0 (80 : BitVec 13)) (B + 84)
      (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
  have hmem0 : ∀ a i,
      CodeReq.singleton (B + 88) (.LD .x21 .x8 0) a = some i →
        segmentsCr a = some i :=
    segments_mem_at 22 (.LD .x21 .x8 0) (B + 88)
      (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
  have hmem1 : ∀ a i,
      CodeReq.singleton (B + 92) (.LD .x22 .x8 8) a = some i →
        segmentsCr a = some i :=
    segments_mem_at 23 (.LD .x22 .x8 8) (B + 92)
      (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
  have hmem2 : ∀ a i,
      CodeReq.singleton (B + 96) (.ADDI .x8 .x8 (16 : BitVec 12)) a = some i →
        segmentsCr a = some i :=
    segments_mem_at 24 (.ADDI .x8 .x8 (16 : BitVec 12)) (B + 96)
      (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
  have hmem3 : ∀ a i,
      CodeReq.singleton (B + 100) (.ADDI .x9 .x9 (-1 : BitVec 12)) a = some i →
        segmentsCr a = some i :=
    segments_mem_at 25 (.ADDI .x9 .x9 (-1 : BitVec 12)) (B + 100)
      (by decide) (by rw [segmentsProgL_len]; decide) (by rfl)
  let d0 : List (BitVec 8) := segmentsDescriptorBytes p0 bs0.length
  let d1 : List (BitVec 8) := segmentsDescriptorBytes p1 bs1.length
  let d2 : List (BitVec 8) := segmentsDescriptorBytes p2 bs2.length
  let st1 : List (BitVec 8) := segmentsStateFold st bs0 0 0 bs0.length
  let st2 : List (BitVec 8) :=
    segmentsStateFold st1 bs1 (segmentsFillAfter 0 bs0.length) 0 bs1.length
  let f1 : Nat := segmentsFillAfter 0 bs0.length
  let f2 : Nat := segmentsFillAfter f1 bs1.length
  let A1 : Assertion :=
    bytesRegion (tableBase + BitVec.ofNat 64 16) d1 **
      bytesRegion (tableBase + BitVec.ofNat 64 32) d2 **
      bytesRegion p1 bs1 ** bytesRegion p2 bs2 ** A
  let A2 : Assertion :=
    bytesRegion tableBase d0 **
      bytesRegion (tableBase + BitVec.ofNat 64 32) d2 **
      bytesRegion p0 bs0 ** bytesRegion p2 bs2 ** A
  let A3 : Assertion :=
    bytesRegion tableBase d0 **
      bytesRegion (tableBase + BitVec.ofNat 64 16) d1 **
      bytesRegion p0 bs0 ** bytesRegion p1 bs1 ** A
  have hA1 : A1.pcFree := by
    simp only [A1]
    pcf; assumption
  have hA2 : A2.pcFree := by
    simp only [A2]
    pcf; assumption
  have hA3 : A3.pcFree := by
    simp only [A3]
    pcf; assumption
  have hst1 : st1.length = 200 := by
    simp only [st1]
    rw [segmentsStateFold_length, hst]
  have hst2 : st2.length = 200 := by
    simp only [st2]
    rw [segmentsStateFold_length, hst1]
  have hf1 : f1 < 136 := by
    simp only [f1]
    exact segmentsFillAfter_lt 0 bs0.length (by decide)
  have hf2 : f2 < 136 := by
    simp only [f2]
    exact segmentsFillAfter_lt f1 bs1.length hf1
  have h0 := segments_outer_iteration_spec scratchBase p0 tableBase st bs0
    0 bs0.length 2 v21 v22 A1 hA1 (by decide) (by decide) hst
    (by exact Nat.le_refl _) hn0 hb8s hb80 hbaseS hbase0 hvalidS hvalid0
    hhead hmem0 hmem1 hmem2 hmem3
  have h1 := segments_outer_iteration_spec scratchBase p1
    (tableBase + BitVec.ofNat 64 16) st1 bs1 f1 bs1.length 1
    (p0 + BitVec.ofNat 64 bs0.length) (0 : Word) A2 hA2 (by decide) hf1 hst1
    (by exact Nat.le_refl _) hn1 hb8s hb81 hbaseS hbase1 hvalidS hvalid1
    hhead hmem0 hmem1 hmem2 hmem3
  have h01 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [A1, A2, d0, d1, d2, st1, f1] at hp ⊢
      xperm_hyp hp)
    h0 h1
  have htable2 :
      (tableBase + BitVec.ofNat 64 16) + BitVec.ofNat 64 16 =
        tableBase + BitVec.ofNat 64 32 := by
    calc
      (tableBase + BitVec.ofNat 64 16) + BitVec.ofNat 64 16 =
          tableBase + (BitVec.ofNat 64 16 + BitVec.ofNat 64 16) := by
            rw [BitVec.add_assoc]
      _ = tableBase + BitVec.ofNat 64 32 := by congr 1
  rw [htable2] at h01
  have h2 := segments_outer_iteration_spec scratchBase p2
    (tableBase + BitVec.ofNat 64 32) st2 bs2 f2 bs2.length 0
    (p1 + BitVec.ofNat 64 bs1.length) (0 : Word) A3 hA3 (by decide) hf2 hst2
    (by exact Nat.le_refl _) hn2 hb8s hb82 hbaseS hbase2 hvalidS hvalid2
    hhead hmem0 hmem1 hmem2 hmem3
  have h012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      simp only [A2, A3, d0, d1, d2, st1, st2, f1, f2] at hp ⊢
      xperm_hyp hp)
    h01 h2
  have htable3 :
      (tableBase + BitVec.ofNat 64 32) + BitVec.ofNat 64 16 =
        tableBase + BitVec.ofNat 64 48 := by
    calc
      (tableBase + BitVec.ofNat 64 32) + BitVec.ofNat 64 16 =
          tableBase + (BitVec.ofNat 64 32 + BitVec.ofNat 64 16) := by
            rw [BitVec.add_assoc]
      _ = tableBase + BitVec.ofNat 64 48 := by congr 1
  rw [htable3] at h012
  have hcount3 : BitVec.ofNat 64 (2 + 1) = (3 : Word) := by decide
  have hcount0 : BitVec.ofNat 64 0 = (0 : Word) := by decide
  simp only [A1, A3, d0, d1, d2, st1, st2, f1, f2] at h012 ⊢
  rw [hcount3, hcount0] at h012
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq)
    h012

end EvmAsm.Codegen.Proofs
