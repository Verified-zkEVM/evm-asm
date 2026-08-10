/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakRem

  Remainder byte XOR-absorb countdown for `zkvm_keccak256`:
  LBU input; LBU state; XOR; SB state; advance both cursors; ADDI ctr -1; BNE.
  Mirrors HashBridgeKeccakDword at byte width. Empty-rem skip is a later outer
  BEQ, not this loop.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakAbsorb
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Stateless.SpecRef

set_option maxRecDepth 8000

/-- Apply one-byte XOR for positions `0..q` of a residual input suffix. -/
def xorBytesUpTo (st : List (BitVec 8)) (inp : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => st
  | q + 1 =>
      let st' := xorBytesUpTo st inp q
      let b := (inp.getD q 0) ^^^ (st'.getD q 0)
      setBytes st' q [b]

theorem xorBytesUpTo_length (st inp : List (BitVec 8)) (q : Nat) :
    (xorBytesUpTo st inp q).length = st.length := by
  induction q generalizing st with
  | zero => rfl
  | succ q ih =>
    simp only [xorBytesUpTo, length_setBytes, ih]

private theorem cursor_advance1 (p : Word) (k : Nat) :
    p + BitVec.ofNat 64 k + signExtend12 (1 : BitVec 12)
      = p + BitVec.ofNat 64 (k + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((1 : Word)).toNat = 1 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

private theorem ctr_dec (n : Nat) (_hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 n := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

/-- Byte XOR after zext64/trunc8 round-trip. -/
private theorem truncate_xor_zeroExtend (a b : BitVec 8) :
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

/-- Inv at remaining `n`: bytes `0..rem-n` XOR'd; temps owned. -/
def keccakRemInv (curS curI : Reg) (scratchBase inputBase : Word)
    (st0 inp : List (BitVec 8)) (rem n : Nat) : Assertion :=
  (curS ↦ᵣ (scratchBase + BitVec.ofNat 64 (rem - n))) **
  (curI ↦ᵣ (inputBase + BitVec.ofNat 64 (rem - n))) **
  bytesRegion scratchBase (xorBytesUpTo st0 inp (rem - n)) **
  bytesRegion inputBase inp **
  (regOwn .x5) ** (regOwn .x6)

theorem keccakRemInv_pcFree (curS curI : Reg) (scratchBase inputBase : Word)
    (st0 inp : List (BitVec 8)) (rem n : Nat) :
    (keccakRemInv curS curI scratchBase inputBase st0 inp rem n).pcFree := by
  unfold keccakRemInv; pcf

/-- Peel two trailing owns. -/
private theorem of_forall2 {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Q : Assertion} {r1 r2 : Reg}
    (htrip : ∀ (v1 v2 : Word),
      cpsTripleWithin n entry exit cr (P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2))
        (Q ** regOwn r1 ** regOwn r2)) :
    cpsTripleWithin n entry exit cr (P ** regOwn r1 ** regOwn r2)
      (Q ** regOwn r1 ** regOwn r2) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hRest, hd0, hu0, hpP0, hpRest⟩ := hpP
  obtain ⟨hR1, hR2c, hd1, hu1, hpR1, hpR2c⟩ := hpRest
  obtain ⟨v1, hv1⟩ := hpR1
  obtain ⟨v2, hv2⟩ := hpR2c
  have hPR' :
      ((P ** (r1 ↦ᵣ v1) ** (r2 ↦ᵣ v2)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hRest, hd0, hu0, hpP0, ⟨hR1, hR2c, hd1, hu1, hv1, hv2⟩⟩, hpR⟩
  exact htrip v1 v2 R hR s hcr hPR' hpc

/-- Concrete-temp body step (7 insn, no BNE). -/
private theorem keccakRemBody_step (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 inp : List (BitVec 8))
    (rem n : Nat) (v5 v6 : Word)
    (hn : n < rem)
    (hst : st0.length = 200)
    (hinp : rem ≤ inp.length)
    (hrem_le : rem ≤ 200)
    (_hrem64 : rem < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hovers : scratchBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : inputBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : isValidByteAccess
      (inputBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hmemLbI : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLbS : ∀ a i, CodeReq.singleton (hdr + 4) (.LBU .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x5 .x5 .x6) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton (hdr + 12) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 1) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 1) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x9 .x9 (-1)) a = some i →
      cr a = some i) :
    let k := rem - (n + 1)
    cpsTripleWithin 7 hdr (hdr + 28) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x9 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (regOwn .x5) ** (regOwn .x6)) := by
  intro k
  have hk_def : k = rem - (n + 1) := rfl
  have hk_lt_rem : k < rem := by
    have : rem - (n + 1) < rem := Nat.sub_lt (Nat.zero_lt_of_lt hn) (by omega)
    simpa [hk_def] using this
  have hk_lt_st : k < (xorBytesUpTo st0 inp k).length := by
    rw [xorBytesUpTo_length, hst]
    exact Nat.lt_of_lt_of_le hk_lt_rem hrem_le
  have hk_lt_in : k < inp.length := Nat.lt_of_lt_of_le hk_lt_rem hinp
  have hst_len : (xorBytesUpTo st0 inp k).length = 200 := by
    rw [xorBytesUpTo_length, hst]
  -- LBU input → x5
  have hlbuI0 := cpsTripleWithin_extend_code hmemLbI
    (bytesRegion_lbu_within .x5 .x30 inputBase v5 hdr inp k
      (by decide) hb8i hk_lt_in hoveri hvalidi)
  have hlbuI : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x5 ↦ᵣ v5) ** bytesRegion inputBase inp)
      ((.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        (.x5 ↦ᵣ ((inp[k]'hk_lt_in).zeroExtend 64)) **
        bytesRegion inputBase inp) := hlbuI0
  have hlbuIF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
      bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
      (.x6 ↦ᵣ v6))
    (by pcf) hlbuI
  have c0 : cpsTripleWithin 1 hdr (hdr + 4) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ ((inp[k]'hk_lt_in).zeroExtend 64)) ** (.x6 ↦ᵣ v6)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlbuIF
  -- LBU state → x6
  have hlbuS0 := cpsTripleWithin_extend_code hmemLbS
    (bytesRegion_lbu_within .x6 .x28 scratchBase v6 (hdr + 4)
      (xorBytesUpTo st0 inp k) k (by decide) hb8s hk_lt_st hovers hvalids)
  have hlbuS : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x6 ↦ᵣ v6) ** bytesRegion scratchBase (xorBytesUpTo st0 inp k))
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x6 ↦ᵣ (((xorBytesUpTo st0 inp k)[k]'hk_lt_st).zeroExtend 64)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k)) := by
    rw [show (hdr + 4 : Word) + 4 = hdr + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hlbuS0
    exact hlbuS0
  have hlbuSF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      bytesRegion inputBase inp **
      (.x5 ↦ᵣ ((inp[k]'hk_lt_in).zeroExtend 64)))
    (by pcf) hlbuS
  have c1 : cpsTripleWithin 1 (hdr + 4) (hdr + 8) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ ((inp[k]'hk_lt_in).zeroExtend 64)) ** (.x6 ↦ᵣ v6))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ ((inp[k]'hk_lt_in).zeroExtend 64)) **
        (.x6 ↦ᵣ (((xorBytesUpTo st0 inp k)[k]'hk_lt_st).zeroExtend 64))) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hlbuSF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  -- XOR x5,x5,x6  (rd = rs1 = x5)
  let vI : Word := (inp[k]'hk_lt_in).zeroExtend 64
  let vS : Word := ((xorBytesUpTo st0 inp k)[k]'hk_lt_st).zeroExtend 64
  have hxor0 := cpsTripleWithin_extend_code hmemXor
    (xor_spec_gen_rd_eq_rs1_within .x5 .x6 vI vS (hdr + 8) (by decide))
  have hxor : cpsTripleWithin 1 (hdr + 8) (hdr + 12) cr
      ((.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ vS))
      ((.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS)) := by
    rw [show (hdr + 8 : Word) + 4 = hdr + 12 from by
      rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]]
      at hxor0
    exact hxor0
  have hxorF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
      bytesRegion inputBase inp)
    (by pcf) hxor
  have c2 : cpsTripleWithin 1 (hdr + 8) (hdr + 12) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ vI) ** (.x6 ↦ᵣ vS))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS)) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hxorF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS] at hq ⊢; xperm_hyp hq
  have c012 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by simp only [vI, vS] at hp ⊢; xperm_hyp hp) c01 c2
  -- SB state byte
  have hsb0 := cpsTripleWithin_extend_code hmemSb
    (bytesRegion_sb_within .x28 .x5 scratchBase (vI ^^^ vS) (hdr + 12)
      (xorBytesUpTo st0 inp k) k hb8s hk_lt_st hovers hvalids)
  have hsb : cpsTripleWithin 1 (hdr + 12) (hdr + 16) cr
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x5 ↦ᵣ (vI ^^^ vS)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k))
      ((.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x5 ↦ᵣ (vI ^^^ vS)) **
        bytesRegion scratchBase
          ((xorBytesUpTo st0 inp k).set k ((vI ^^^ vS).truncate 8))) := by
    rw [show (hdr + 12 : Word) + 4 = hdr + 16 from by
      rw [BitVec.add_assoc, show ((12 : Word) + 4) = (16 : Word) from by decide]]
      at hsb0
    exact hsb0
  have hsbF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      bytesRegion inputBase inp **
      (.x6 ↦ᵣ vS))
    (by pcf) hsb
  have hxor_set :
      (xorBytesUpTo st0 inp k).set k ((vI ^^^ vS).truncate 8)
        = xorBytesUpTo st0 inp (k + 1) := by
    have hgetI : inp.getD k 0 = inp[k]'hk_lt_in := by
      simp [List.getD, List.getElem?_eq_getElem hk_lt_in]
    have hgetS : (xorBytesUpTo st0 inp k).getD k 0 =
        (xorBytesUpTo st0 inp k)[k]'hk_lt_st := by
      simp [List.getD, List.getElem?_eq_getElem hk_lt_st]
    have htrunc :
        ((vI ^^^ vS).truncate 8)
          = (inp[k]'hk_lt_in) ^^^ (xorBytesUpTo st0 inp k)[k]'hk_lt_st := by
      simp only [vI, vS]
      exact truncate_xor_zeroExtend _ _
    calc
      (xorBytesUpTo st0 inp k).set k ((vI ^^^ vS).truncate 8)
          = (xorBytesUpTo st0 inp k).set k
              ((inp[k]'hk_lt_in) ^^^ (xorBytesUpTo st0 inp k)[k]'hk_lt_st) := by
            rw [htrunc]
      _ = setBytes (xorBytesUpTo st0 inp k) k
              [(inp[k]'hk_lt_in) ^^^ (xorBytesUpTo st0 inp k)[k]'hk_lt_st] :=
            (setBytes_singleton _ _ _).symm
      _ = setBytes (xorBytesUpTo st0 inp k) k
              [(inp.getD k 0) ^^^ ((xorBytesUpTo st0 inp k).getD k 0)] := by
            rw [hgetI, hgetS]
      _ = xorBytesUpTo st0 inp (k + 1) := rfl
  have c3 : cpsTripleWithin 1 (hdr + 12) (hdr + 16) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp k) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS)) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hsbF
    · simp only [vI, vS] at hp ⊢; xperm_hyp hp
    · simp only [vI, vS, hxor_set] at hq ⊢; xperm_hyp hq
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  -- ADDI x28 +1
  have haddS0 := cpsTripleWithin_extend_code hmemAddS
    (addi_spec_gen_same_within .x28 (scratchBase + BitVec.ofNat 64 k) 1
      (hdr + 16) (by decide))
  have haddS : cpsTripleWithin 1 (hdr + 16) (hdr + 20) cr
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k))
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) := by
    rw [show (hdr + 16 : Word) + 4 = hdr + 20 from by
      rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]]
      at haddS0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        have hq' := hq
        rw [cursor_advance1 scratchBase k] at hq'
        exact hq') haddS0
  have haddSF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
      bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
      bytesRegion inputBase inp **
      (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
    (by pcf) haddS
  have c4 : cpsTripleWithin 1 (hdr + 16) (hdr + 20) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 k)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddSF
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 c4
  -- ADDI x30 +1
  have haddI0 := cpsTripleWithin_extend_code hmemAddI
    (addi_spec_gen_same_within .x30 (inputBase + BitVec.ofNat 64 k) 1
      (hdr + 20) (by decide))
  have haddI : cpsTripleWithin 1 (hdr + 20) (hdr + 24) cr
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k))
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) := by
    rw [show (hdr + 20 : Word) + 4 = hdr + 24 from by
      rw [BitVec.add_assoc, show ((20 : Word) + 4) = (24 : Word) from by decide]]
      at haddI0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        have hq' := hq
        rw [cursor_advance1 inputBase k] at hq'
        exact hq') haddI0
  have haddIF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
      bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
      bytesRegion inputBase inp **
      (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
    (by pcf) haddI
  have c5 : cpsTripleWithin 1 (hdr + 20) (hdr + 24) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 k)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddIF
  have c012345 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01234 c5
  -- ADDI x9 -1
  have hn64 : n + 1 < 2 ^ 64 := by omega
  have haddC0 := cpsTripleWithin_extend_code hmemAddC
    (addi_spec_gen_same_within .x9 (BitVec.ofNat 64 (n + 1)) (-1)
      (hdr + 24) (by decide))
  have haddC : cpsTripleWithin 1 (hdr + 24) (hdr + 28) cr
      (.x9 ↦ᵣ BitVec.ofNat 64 (n + 1))
      (.x9 ↦ᵣ BitVec.ofNat 64 n) := by
    rw [show (hdr + 24 : Word) + 4 = hdr + 28 from by
      rw [BitVec.add_assoc, show ((24 : Word) + 4) = (28 : Word) from by decide]]
      at haddC0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by
        have hq' := hq
        rw [ctr_dec n hn64] at hq'
        exact hq') haddC0
  have haddCF := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
      (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
      (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
      bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
      bytesRegion inputBase inp **
      (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
    (by pcf) haddC
  have c6 : cpsTripleWithin 1 (hdr + 24) (hdr + 28) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS))
      ((.x9 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (k + 1))) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (k + 1))) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp (k + 1)) **
        bytesRegion inputBase inp **
        (.x5 ↦ᵣ (vI ^^^ vS)) ** (.x6 ↦ᵣ vS)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddCF
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012345 c6
  -- Drop concrete x5/x6 to owns in post
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) cAll
  exact (sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono
                (regIs_implies_regOwn .x5)
                (regIs_implies_regOwn .x6)))))))) _ hq

/-- Body under owns (for loop). -/
theorem keccakRemBody_spec (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 inp : List (BitVec 8))
    (rem n : Nat)
    (hn : n < rem)
    (hst : st0.length = 200)
    (hinp : rem ≤ inp.length)
    (hrem_le : rem ≤ 200)
    (hrem64 : rem < 2 ^ 64)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hovers : scratchBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : inputBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : isValidByteAccess
      (scratchBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : isValidByteAccess
      (inputBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hmemLbI : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLbS : ∀ a i, CodeReq.singleton (hdr + 4) (.LBU .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x5 .x5 .x6) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton (hdr + 12) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 1) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 1) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x9 .x9 (-1)) a = some i →
      cr a = some i) :
    cpsTripleWithin 7 hdr (hdr + 28) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem (n + 1))
      ((.x9 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem n) := by
  let P : Assertion :=
    (.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (rem - (n + 1)))) **
    (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (rem - (n + 1)))) **
    bytesRegion scratchBase (xorBytesUpTo st0 inp (rem - (n + 1))) **
    bytesRegion inputBase inp
  let Q : Assertion :=
    (.x9 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 (rem - n))) **
    (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 (rem - n))) **
    bytesRegion scratchBase (xorBytesUpTo st0 inp (rem - n)) **
    bytesRegion inputBase inp
  have hforall := of_forall2 (P := P) (Q := Q) (r1 := .x5) (r2 := .x6)
    (fun v1 v2 => by
      have h :=
        keccakRemBody_step cr hdr scratchBase inputBase st0 inp rem n v1 v2
          hn hst hinp hrem_le hrem64 hb8s hb8i hovers hoveri hvalids hvalidi
          hmemLbI hmemLbS hmemXor hmemSb hmemAddS hmemAddI hmemAddC
      have hk1 : rem - (n + 1) + 1 = rem - n := by omega
      refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) h
      · simp only [P] at hp ⊢; xperm_hyp hp
      · simp only [Q, hk1] at hq ⊢; xperm_hyp hq)
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hforall
  · simp only [keccakRemInv, P] at hp ⊢; xperm_hyp hp
  · simp only [keccakRemInv, Q] at hq ⊢; xperm_hyp hq

/-- Full `rem`-step remainder XOR loop (rem ≥ 1). -/
theorem keccakRemLoop_full (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 inp : List (BitVec 8)) (rem : Nat)
    (hrem_pos : 1 ≤ rem) (hrem_le : rem ≤ 200) (hrem64 : rem < 2 ^ 64)
    (hst : st0.length = 200)
    (hinp : rem ≤ inp.length)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      scratchBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      inputBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (scratchBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess (inputBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hmemLbI : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLbS : ∀ a i, CodeReq.singleton (hdr + 4) (.LBU .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x5 .x5 .x6) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton (hdr + 12) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 1) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 1) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x9 .x9 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 28) (.BNE .x9 .x0 (-28)) a = some i →
      cr a = some i) :
    cpsTripleWithin (rem * 8) hdr (hdr + 32) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem rem)
      ((.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem 0) := by
  have hbody : ∀ n, n < rem →
      cpsTripleWithin 7 hdr (hdr + 28) cr
        ((.x9 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (.x0 ↦ᵣ (0 : Word)) **
          keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem (n + 1))
        ((.x9 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word)) **
          keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem n) :=
    fun n hn =>
      keccakRemBody_spec cr hdr scratchBase inputBase st0 inp rem n hn
        hst hinp hrem_le hrem64 hb8s hb8i (hovers n hn) (hoveri n hn)
        (hvalids n hn) (hvalidi n hn)
        hmemLbI hmemLbS hmemXor hmemSb hmemAddS hmemAddI hmemAddC
  have hloop := countdownLoopBottom_spec cr hdr (hdr + 28) .x9
    (-28 : BitVec 13) 7 rem
    (keccakRemInv .x28 .x30 scratchBase inputBase st0 inp rem)
    (by decide) hrem_pos hrem64
    (by
      rw [show signExtend13 (-28 : BitVec 13) = (-28 : Word) from by decide]
      bv_omega)
    (fun n => keccakRemInv_pcFree .x28 .x30 scratchBase inputBase st0 inp rem n)
    hmemBne hbody
  rw [show rem * (7 + 1) = rem * 8 by omega,
    show hdr + 28 + 4 = hdr + 32 from by
      rw [BitVec.add_assoc, show ((28 : Word) + 4) = (32 : Word) from by decide]]
    at hloop
  exact hloop

/-- Entry form: cursors at bases, state at entry, ctr=rem. -/
theorem keccakRemLoop_entry (cr : CodeReq) (hdr : Word)
    (scratchBase inputBase : Word) (st0 inp : List (BitVec 8)) (rem : Nat)
    (hrem_pos : 1 ≤ rem) (hrem_le : rem ≤ 200) (hrem64 : rem < 2 ^ 64)
    (hst : st0.length = 200)
    (hinp : rem ≤ inp.length)
    (hb8s : scratchBase.toNat % 8 = 0)
    (hb8i : inputBase.toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      scratchBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      inputBase.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (scratchBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess (inputBase + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hmemLbI : ∀ a i, CodeReq.singleton hdr (.LBU .x5 .x30 0) a = some i →
      cr a = some i)
    (hmemLbS : ∀ a i, CodeReq.singleton (hdr + 4) (.LBU .x6 .x28 0) a = some i →
      cr a = some i)
    (hmemXor : ∀ a i, CodeReq.singleton (hdr + 8) (.XOR .x5 .x5 .x6) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton (hdr + 12) (.SB .x28 .x5 0) a = some i →
      cr a = some i)
    (hmemAddS : ∀ a i, CodeReq.singleton (hdr + 16) (.ADDI .x28 .x28 1) a = some i →
      cr a = some i)
    (hmemAddI : ∀ a i, CodeReq.singleton (hdr + 20) (.ADDI .x30 .x30 1) a = some i →
      cr a = some i)
    (hmemAddC : ∀ a i, CodeReq.singleton (hdr + 24) (.ADDI .x9 .x9 (-1)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i, CodeReq.singleton (hdr + 28) (.BNE .x9 .x0 (-28)) a = some i →
      cr a = some i) :
    cpsTripleWithin (rem * 8) hdr (hdr + 32) cr
      ((.x9 ↦ᵣ BitVec.ofNat 64 rem) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ scratchBase) ** (.x30 ↦ᵣ inputBase) **
        bytesRegion scratchBase st0 ** bytesRegion inputBase inp **
        (regOwn .x5) ** (regOwn .x6))
      ((.x9 ↦ᵣ BitVec.ofNat 64 0) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x28 ↦ᵣ (scratchBase + BitVec.ofNat 64 rem)) **
        (.x30 ↦ᵣ (inputBase + BitVec.ofNat 64 rem)) **
        bytesRegion scratchBase (xorBytesUpTo st0 inp rem) **
        bytesRegion inputBase inp **
        (regOwn .x5) ** (regOwn .x6)) := by
  have hfull :=
    keccakRemLoop_full cr hdr scratchBase inputBase st0 inp rem
      hrem_pos hrem_le hrem64 hst hinp hb8s hb8i hovers hoveri hvalids hvalidi
      hmemLbI hmemLbS hmemXor hmemSb hmemAddS hmemAddI hmemAddC hmemBne
  refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hfull
  · unfold keccakRemInv
    rw [show rem - rem = 0 from by omega,
      show scratchBase + BitVec.ofNat 64 0 = scratchBase from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega,
      show inputBase + BitVec.ofNat 64 0 = inputBase from by
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]; bv_omega,
      show xorBytesUpTo st0 inp 0 = st0 from rfl]
    xperm_hyp hp
  · unfold keccakRemInv at hq
    rw [show rem - 0 = rem from by omega] at hq
    xperm_hyp hq

end EvmAsm.Codegen.Proofs
