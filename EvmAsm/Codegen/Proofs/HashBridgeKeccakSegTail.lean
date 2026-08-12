/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakSegTail

  The **tail** of `zkvm_keccak256_segments`: everything from the `.Lkss_done`
  label (`KssB+164`, program index 41) to the body exit (`KssB+240`, index 60),
  i.e. the 19 instructions that turn a partially-filled sponge into the 32-byte
  digest and the success status.

  ## What the tail computes

  On entry the 200-byte sponge arena `zk3_state` holds the state `st` after all
  segment bytes have been absorbed, and `s4` (`x20`) holds the **rate-block fill
  offset** `fill ∈ [0, 136)` — the number of bytes XOR-ed into the current rate
  block since the last permutation.  The tail then does:

  1. `add t1, s3, s4` — materialise the byte cursor `zk3_state + fill`
     (this instruction is what `zkvm_keccak256` does not have: there the cursor
     was already live in `x28`, here it must be recomputed from the carried
     fill counter).
  2. **pad10\*1**, in the pre-NIST Keccak flavour: XOR `0x01` into the state
     byte at offset `fill`, then XOR `0x80` into the state byte at offset 135
     (the last byte of the 136-byte rate block).  ⚠️ When `fill = 135` the two
     writes hit the SAME byte and collapse to `0x81` — that is not a special
     case in the code, it falls out of doing the two XORs in sequence, and the
     pure model `keccakGuestPad` mirrors it exactly (its second `setBytes`
     reads back the byte the first one wrote).
  3. `csrs 0x800` — the final Keccak-f[1600] permutation, in place over the
     25 lanes at `zk3_state`.
  4. **squeeze**: four `ld`/`sd` pairs copy lanes 0..3 (32 bytes) to the
     caller's output buffer.
  5. `li a0, 0` — success status.

  ## Relationship to the `zkvm_keccak256` proof

  This is the same instruction sequence as `keccakPadCsrsDigestLi0_spec`
  (`HashBridgeKeccakWrap`), under a different register assignment — segments
  uses `s3`/`x19` for the sponge base, `t1`/`x6` for the byte cursor and
  `t2`/`x7` for the pad temporary, where `zkvm_keccak256` uses `s0`/`x8`,
  `t3`/`x28` and `t0`/`x5`.  The register-generic primitives
  (`bytesRegion_lbu_within`, `bytesRegion_sb_within`, `bytesRegion_ld_within`,
  `bytesRegion_sd_within`, `csrs_keccak_x10_own_flat`) are reused directly; the
  register-specific compose lemmas are re-derived here rather than instantiated,
  because the originals hardcode `x28`/`x5`/`x8`.

  Because the post is stated with `keccakGuestPad`, `keccakBytes` and
  `keccakDigestCopy` — the *same* pure functions the landed
  `zkvm_keccak256_spec_within` post uses — the SpecRef bridge
  `keccakBodyDigest_eq_specref` (#12104) applies to this routine's output with
  no re-derivation, provided the caller supplies the sponge image.

  ## Footprint

  Every cell the tail writes is named: the 200-byte `zk3_state` arena
  (`bytesRegion KssZk3 …` in BOTH pre and post) and the 32-byte output buffer.
  The exposed temporaries the `csrs` may clobber are carried as `regOwns` rather
  than left unmentioned, so a universally-quantified frame cannot own them.

  No elaboration budget is widened in this module beyond `maxRecDepth`.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakSegSetup
import EvmAsm.Codegen.Proofs.HashBridgeKeccakWrap
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## Pure-arithmetic helpers (register-agnostic) -/

private theorem kss_xor_zext_byte (b pad : BitVec 8) :
    (b.zeroExtend 64) ^^^ (pad.zeroExtend 64) = (b ^^^ pad).zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  have hb : b.toNat < 256 := b.isLt
  have hp : pad.toNat < 256 := pad.isLt
  have hb64 : b.toNat < 2 ^ 64 := by omega
  have hp64 : pad.toNat < 2 ^ 64 := by omega
  have hx : b.toNat ^^^ pad.toNat < 256 := by
    have := (b ^^^ pad).isLt; rwa [BitVec.toNat_xor] at this
  have hx64 : b.toNat ^^^ pad.toNat < 2 ^ 64 := by omega
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt hx64]

/-- Peel a trailing `regOwn r` from a precondition into a universally
    quantified concrete value (the `of_forall1` of `HashBridgeKeccakWrap`,
    which is `private` there). -/
private theorem of_forall1 {n : Nat} {entry exit : Word} {cr : CodeReq}
    {P Q : Assertion} {r : Reg}
    (h : ∀ v, cpsTripleWithin n entry exit cr (P ** (r ↦ᵣ v)) Q) :
    cpsTripleWithin n entry exit cr (P ** regOwn r) Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨hMem, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hP0, hOwn, hd0, hu0, hp0, hpOwn⟩ := hpP
  obtain ⟨v, hv⟩ := hpOwn
  have hPR' : ((P ** (r ↦ᵣ v)) ** R).holdsFor s :=
    ⟨hMem, hcompat, h_P, h_R, hdisj, hunion,
      ⟨hP0, hOwn, hd0, hu0, hp0, hv⟩, hpR⟩
  exact h v R hR s hcr hPR' hpc

/-! ## One pad byte, register-generic

    `LBU vr, 0(pr)` ; `XORI vr, vr, imm` ; `SB vr, 0(pr)` — a read-modify-write
    of the single state byte the cursor `pr` points at.  This is
    `keccakPadByte_step` with the two registers lifted to parameters. -/

theorem kssPadByte_step (cr : CodeReq) (entry : Word) (pr vr : Reg)
    (scratchBase : Word) (st : List (BitVec 8)) (off : Nat)
    (imm : BitVec 12) (pad : BitVec 8) (vOld : Word)
    (hvr : vr ≠ .x0)
    (himm : signExtend12 imm = pad.zeroExtend 64)
    (hst : st.length = 200) (hoff : off < 200)
    (halign : scratchBase.toNat % 8 = 0)
    (h_over : scratchBase.toNat + 200 ≤ 2 ^ 64)
    (hvalidB : isValidByteAccess (scratchBase + BitVec.ofNat 64 off) = true)
    (hmemLb : ∀ a i, CodeReq.singleton entry (.LBU vr pr 0) a = some i →
      cr a = some i)
    (hmemXi : ∀ a i, CodeReq.singleton (entry + 4) (.XORI vr vr imm) a = some i →
      cr a = some i)
    (hmemSb : ∀ a i, CodeReq.singleton (entry + 8) (.SB pr vr 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 entry (entry + 12) cr
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ vOld) ** bytesRegion scratchBase st)
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (regOwn vr) **
        bytesRegion scratchBase
          (setBytes st off [(st.getD off 0) ^^^ pad])) := by
  have hi : off < st.length := by omega
  have hover : scratchBase.toNat + off < 2 ^ 64 := by omega
  -- LBU
  have hlbu0 := cpsTripleWithin_extend_code hmemLb
    (bytesRegion_lbu_within vr pr scratchBase vOld entry st off
      hvr halign hi hover hvalidB)
  have hlbu : cpsTripleWithin 1 entry (entry + 4) cr
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ vOld) ** bytesRegion scratchBase st)
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ ((st[off]'hi).zeroExtend 64)) **
        bytesRegion scratchBase st) := hlbu0
  -- XORI
  have hxori0 := cpsTripleWithin_extend_code hmemXi
    (xori_spec_gen_same_within vr ((st[off]'hi).zeroExtend 64) imm
      (entry + 4) hvr)
  have hxori : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      (vr ↦ᵣ ((st[off]'hi).zeroExtend 64))
      (vr ↦ᵣ (((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm)) := by
    rw [show (entry + 4 : Word) + 4 = entry + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hxori0
    exact hxori0
  have hxoriF := cpsTripleWithin_frameR
    ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) ** bytesRegion scratchBase st)
    (by pcf) hxori
  have c1 : cpsTripleWithin 1 (entry + 4) (entry + 8) cr
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ ((st[off]'hi).zeroExtend 64)) **
        bytesRegion scratchBase st)
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ (((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm)) **
        bytesRegion scratchBase st) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hxoriF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlbu c1
  -- SB
  let vX : Word := ((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm
  have hsb0 := cpsTripleWithin_extend_code hmemSb
    (bytesRegion_sb_within pr vr scratchBase vX (entry + 8) st off
      halign hi hover hvalidB)
  have hsb : cpsTripleWithin 1 (entry + 8) (entry + 12) cr
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ vX) ** bytesRegion scratchBase st)
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ vX) **
        bytesRegion scratchBase (st.set off (vX.truncate 8))) := by
    rw [show (entry + 8 : Word) + 4 = entry + 12 from by
      rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]]
      at hsb0
    exact hsb0
  have hset :
      st.set off (vX.truncate 8) =
        setBytes st off [(st.getD off 0) ^^^ pad] := by
    have hget : st.getD off 0 = st[off]'hi := by
      simp [List.getD, List.getElem?_eq_getElem hi]
    have htrunc : vX.truncate 8 = (st[off]'hi) ^^^ pad := by
      simp only [vX, himm]
      rw [kss_xor_zext_byte, truncate_zeroExtend_byte]
    calc
      st.set off (vX.truncate 8)
          = st.set off ((st[off]'hi) ^^^ pad) := by rw [htrunc]
      _ = setBytes st off [(st[off]'hi) ^^^ pad] := (setBytes_singleton _ _ _).symm
      _ = setBytes st off [(st.getD off 0) ^^^ pad] := by rw [hget]
  have c2 : cpsTripleWithin 1 (entry + 8) (entry + 12) cr
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ (((st[off]'hi).zeroExtend 64) ^^^ signExtend12 imm)) **
        bytesRegion scratchBase st)
      ((pr ↦ᵣ (scratchBase + BitVec.ofNat 64 off)) **
        (vr ↦ᵣ vX) **
        bytesRegion scratchBase (setBytes st off [(st.getD off 0) ^^^ pad])) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hsb
    · simp only [vX] at hp ⊢; xperm_hyp hp
    · simp only [vX, hset] at hq ⊢; xperm_hyp hq
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) c012
  simp only [vX] at hq
  exact (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn vr))) _ hq

/-! ## The pad block: `KssB+164 → KssB+196` (8 instructions)

    `add t1,s3,s4` ; pad `0x01` at `fill` ; `addi t1,s3,135` ; pad `0x80` at 135. -/

theorem kssPadBlock_spec (st : List (BitVec 8)) (fill : Nat) (v6 v7 : Word)
    (hst : st.length = 200) (hfill : fill ≤ 135)
    (halign : KssZk3.toNat % 8 = 0)
    (h_over : KssZk3.toNat + 200 ≤ 2 ^ 64)
    (hvalidFill : isValidByteAccess (KssZk3 + BitVec.ofNat 64 fill) = true)
    (hvalid135 : isValidByteAccess (KssZk3 + BitVec.ofNat 64 135) = true) :
    cpsTripleWithin 8 (KssB + 164) (KssB + 196) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** bytesRegion KssZk3 st)
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3 (keccakGuestPad st fill)) := by
  have hfill200 : fill < 200 := by omega
  have h135_200 : (135 : Nat) < 200 := by omega
  -- (1) ADD t1, s3, s4  → t1 = zk3 + fill
  have hadd0 := cpsTripleWithin_extend_code
    (kss_mem_at 41 (.ADD .x6 .x19 .x20) (KssB + 164) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (add_spec_gen_within .x6 .x19 .x20 KssZk3 (BitVec.ofNat 64 fill) v6
      (KssB + 164) (by decide))
  have hadd : cpsTripleWithin 1 (KssB + 164) (KssB + 168) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (.x6 ↦ᵣ v6))
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 fill))) := by
    rwa [show (KssB + 164 : Word) + 4 = KssB + 168 from by decide] at hadd0
  have haddF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** bytesRegion KssZk3 st)
    (pcFree_sepConj (by pcf) (bytesRegion_pcFree _ _)) hadd
  have c0 : cpsTripleWithin 1 (KssB + 164) (KssB + 168) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** bytesRegion KssZk3 st)
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 fill)) ** (.x7 ↦ᵣ v7) **
        bytesRegion KssZk3 st) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) haddF
  -- (2) pad 0x01 at offset `fill`
  have hp1 := kssPadByte_step kssCr (KssB + 168) .x6 .x7 KssZk3 st fill
    (1 : BitVec 12) (1 : BitVec 8) v7 (by decide) (by decide)
    hst hfill200 halign h_over hvalidFill
    (kss_mem_at 42 (.LBU .x7 .x6 0) (KssB + 168) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (by
      have h := kss_mem_at 43 (.XORI .x7 .x7 1) (KssB + 172) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 168 : Word) + 4 = KssB + 172 from by decide])
    (by
      have h := kss_mem_at 44 (.SB .x6 .x7 0) (KssB + 176) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 168 : Word) + 8 = KssB + 176 from by decide])
  rw [show (KssB + 168 : Word) + 12 = KssB + 180 from by decide] at hp1
  set st1 : List (BitVec 8) := setBytes st fill [(st.getD fill 0) ^^^ (1 : BitVec 8)]
    with hst1def
  have hst1 : st1.length = 200 := by
    simp only [hst1def, length_setBytes, hst]
  have hp1F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill))
    (by pcf) hp1
  have c1 : cpsTripleWithin 3 (KssB + 168) (KssB + 180) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 fill)) ** (.x7 ↦ᵣ v7) **
        bytesRegion KssZk3 st)
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 fill)) ** (regOwn .x7) **
        bytesRegion KssZk3 st1) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hp1F
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  -- (3) ADDI t1, s3, 135 → t1 = zk3 + 135
  have hadi0 := cpsTripleWithin_extend_code
    (kss_mem_at 45 (.ADDI .x6 .x19 (135 : BitVec 12)) (KssB + 180) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (addi_spec_gen_within .x6 .x19 (KssZk3 + BitVec.ofNat 64 fill) KssZk3
      (135 : BitVec 12) (KssB + 180) (by decide))
  have hadi : cpsTripleWithin 1 (KssB + 180) (KssB + 184) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 fill)))
      ((.x19 ↦ᵣ KssZk3) ** (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135))) := by
    rw [show (KssB + 180 : Word) + 4 = KssB + 184 from by decide] at hadi0
    refine cpsTripleWithin_weaken (fun _ hp => hp) (fun _ hq => ?_) hadi0
    rwa [show KssZk3 + signExtend12 (135 : BitVec 12)
        = KssZk3 + BitVec.ofNat 64 135 from by decide] at hq
  have hadiF := cpsTripleWithin_frameR
    ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x7) ** bytesRegion KssZk3 st1)
    (pcFree_sepConj (by pcf)
      (pcFree_sepConj (by pcf) (bytesRegion_pcFree _ _))) hadi
  have c2 : cpsTripleWithin 1 (KssB + 180) (KssB + 184) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 fill)) ** (regOwn .x7) **
        bytesRegion KssZk3 st1)
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3 st1) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hadiF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  -- (4) pad 0x80 at offset 135 (own x7 → concrete via of_forall1-style peel)
  have hp2core (v7' : Word) := kssPadByte_step kssCr (KssB + 184) .x6 .x7 KssZk3 st1
    135 (128 : BitVec 12) (0x80 : BitVec 8) v7' (by decide) (by decide)
    hst1 h135_200 halign h_over hvalid135
    (kss_mem_at 46 (.LBU .x7 .x6 0) (KssB + 184) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (by
      have h := kss_mem_at 47 (.XORI .x7 .x7 128) (KssB + 188) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 184 : Word) + 4 = KssB + 188 from by decide])
    (by
      have h := kss_mem_at 48 (.SB .x6 .x7 0) (KssB + 192) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 184 : Word) + 8 = KssB + 192 from by decide])
  have hp2own : cpsTripleWithin 3 (KssB + 184) (KssB + 196) kssCr
      ((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3 st1)
      ((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3
          (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)])) := by
    have hstep (v7' : Word) :
        cpsTripleWithin 3 (KssB + 184) (KssB + 196) kssCr
          (((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) **
              bytesRegion KssZk3 st1) ** (.x7 ↦ᵣ v7'))
          ((.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
            bytesRegion KssZk3
              (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)])) := by
      have h := hp2core v7'
      rw [show (KssB + 184 : Word) + 12 = KssB + 196 from by decide] at h
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) h
    have hown := of_forall1 hstep
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hown
  have hp2F := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill))
    (by pcf) hp2own
  have c3 : cpsTripleWithin 3 (KssB + 184) (KssB + 196) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3 st1)
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3
          (setBytes st1 135 [(st1.getD 135 0) ^^^ (0x80 : BitVec 8)])) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hp2F
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  have cFinal := cpsTripleWithin_weaken (fun _ (hp : _) => hp)
    (fun _ hq => by simpa [keccakGuestPad, hst1def] using hq) cAll
  exact cpsTripleWithin_mono_nSteps (by omega) cFinal

/-! ## The final permutation: `KssB+196 → KssB+204`

    `mv a0, s3` ; `csrs 0x800, a0`. -/

theorem kssFinalCsrs_spec (st : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200)
    (halign : KssZk3.toNat % 8 = 0)
    (hvalid : ∀ j, j < 200 →
      isValidMemAddr (KssZk3 + BitVec.ofNat 64 j) = true)
    (v10 : Word) :
    cpsTripleWithin 2 (KssB + 196) (KssB + 204) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ v10) **
        regOwns keccakCsrsRest ** bytesRegion KssZk3 st ** A)
      ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ KssZk3) **
        regOwns keccakCsrsRest **
        bytesRegion KssZk3 (setBytes st 0 (keccakBytes st 0)) ** A) := by
  have hmv := cpsTripleWithin_extend_code
    (kss_mem_at 49 (.MV .x10 .x19) (KssB + 196) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    (mv_spec_gen_within .x10 .x19 KssZk3 v10 (KssB + 196) (by decide))
  rw [show (KssB + 196 : Word) + 4 = KssB + 200 from by decide] at hmv
  have hmvF := cpsTripleWithin_frameR
    (regOwns keccakCsrsRest ** bytesRegion KssZk3 st ** A)
    (pcFree_sepConj (pcFree_regOwns _)
      (pcFree_sepConj (bytesRegion_pcFree _ _) hA)) hmv
  have c0 : cpsTripleWithin 1 (KssB + 196) (KssB + 200) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ v10) **
        regOwns keccakCsrsRest ** bytesRegion KssZk3 st ** A)
      ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ KssZk3) **
        regOwns keccakCsrsRest ** bytesRegion KssZk3 st ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hmvF
  have hcsrs0 := csrs_keccak_x10_own_flat (KssB + 200) KssZk3 st
    ((.x19 ↦ᵣ KssZk3) ** A)
    (pcFree_sepConj (by pcf) hA) hst halign hvalid
  rw [show (KssB + 200 : Word) + 4 = KssB + 204 from by decide] at hcsrs0
  have hcsrs := cpsTripleWithin_extend_code
    (kss_mem_at 50 (.CSRS (2048 : BitVec 12) .x10) (KssB + 200) (by decide)
      (by rw [kssProgL_len]; decide) (by rfl))
    hcsrs0
  have c1 : cpsTripleWithin 1 (KssB + 200) (KssB + 204) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ KssZk3) **
        regOwns keccakCsrsRest ** bytesRegion KssZk3 st ** A)
      ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ KssZk3) **
        regOwns keccakCsrsRest **
        bytesRegion KssZk3 (setBytes st 0 (keccakBytes st 0)) ** A) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hcsrs
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-! ## The squeeze: `KssB+204 → KssB+236` (four `ld`/`sd` pairs) -/

/-- One lane copy: `ld t0, 8q(s3)` ; `sd t0, 8q(s2)`. -/
theorem kssDigestDword_spec (entry : Word) (outputBase : Word)
    (st out : List (BitVec 8)) (q : Nat) (v5 : Word)
    (hst : st.length = 200) (hout : out.length = 32) (hq : q < 4)
    (hmemLd : ∀ a i, CodeReq.singleton entry
        (.LD .x5 .x19 (BitVec.ofNat 12 (8 * q))) a = some i → kssCr a = some i)
    (hmemSd : ∀ a i, CodeReq.singleton (entry + 4)
        (.SD .x18 .x5 (BitVec.ofNat 12 (8 * q))) a = some i → kssCr a = some i) :
    cpsTripleWithin 2 entry (entry + 8) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ v5) **
        bytesRegion KssZk3 st ** bytesRegion outputBase out)
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion KssZk3 st **
        bytesRegion outputBase
          (setBytes out (8 * q) ((st.drop (8 * q)).take 8))) := by
  have hq_st : 8 * q < st.length := by omega
  have hq_out : 8 * q + 8 ≤ out.length := by omega
  have himm : 8 * q < 2 ^ 11 := by omega
  have hld0 := cpsTripleWithin_extend_code hmemLd
    (bytesRegion_ld_within .x5 .x19 KssZk3 v5 entry st q
      (by decide) hq_st himm)
  have hldF := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outputBase) ** bytesRegion outputBase out)
    (pcFree_sepConj (by pcf) (bytesRegion_pcFree _ _)) hld0
  have c0 : cpsTripleWithin 1 entry (entry + 4) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ v5) **
        bytesRegion KssZk3 st ** bytesRegion outputBase out)
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion KssZk3 st ** bytesRegion outputBase out) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq' => by xperm_hyp hq') hldF
  let vD : Word := packBytes ((st.drop (8 * q)).take 8)
  have hsd0 := cpsTripleWithin_extend_code hmemSd
    (bytesRegion_sd_within .x18 .x5 outputBase vD (entry + 4) out q
      hq_out himm)
  have hsd : cpsTripleWithin 1 (entry + 4) (entry + 8) kssCr
      ((.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ vD) ** bytesRegion outputBase out)
      ((.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ vD) **
        bytesRegion outputBase (setBytes out (8 * q) (dwordBytes vD))) := by
    rw [show (entry + 4 : Word) + 4 = entry + 8 from by
      rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
      at hsd0
    exact hsd0
  have hsdF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ KssZk3) ** bytesRegion KssZk3 st)
    (pcFree_sepConj (by pcf) (bytesRegion_pcFree _ _)) hsd
  have hlen : ((st.drop (8 * q)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, hst]; omega
  have hdw : dwordBytes vD = (st.drop (8 * q)).take 8 := by
    simp only [vD]; exact dwordBytes_packBytes _ hlen
  have c1 : cpsTripleWithin 1 (entry + 4) (entry + 8) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion KssZk3 st ** bytesRegion outputBase out)
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
        (.x5 ↦ᵣ packBytes ((st.drop (8 * q)).take 8)) **
        bytesRegion KssZk3 st **
        bytesRegion outputBase
          (setBytes out (8 * q) ((st.drop (8 * q)).take 8))) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq' => ?_) hsdF
    · simp only [vD] at hp ⊢; xperm_hyp hp
    · simp only [vD, hdw] at hq' ⊢; xperm_hyp hq'
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1

/-- All four lane copies: `KssB+204 → KssB+236`. -/
theorem kssDigestAll_spec (outputBase : Word) (st : List (BitVec 8)) (v5 : Word)
    (hst : st.length = 200) :
    cpsTripleWithin 8 (KssB + 204) (KssB + 236) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (.x5 ↦ᵣ v5) **
        bytesRegion KssZk3 st **
        bytesRegion outputBase (List.replicate 32 (0 : BitVec 8)))
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
        bytesRegion KssZk3 st **
        bytesRegion outputBase (keccakDigestCopy st)) := by
  let out0 := List.replicate 32 (0 : BitVec 8)
  have hout0 : out0.length = 32 := by simp only [out0, List.length_replicate]
  have c0 := kssDigestDword_spec (KssB + 204) outputBase st out0 0 v5
    hst hout0 (by omega)
    (kss_mem_at 51 (.LD .x5 .x19 (BitVec.ofNat 12 (8 * 0))) (KssB + 204)
      (by decide) (by rw [kssProgL_len]; decide) (by rfl))
    (by
      have h := kss_mem_at 52 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 0))) (KssB + 208)
        (by decide) (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 204 : Word) + 4 = KssB + 208 from by decide])
  rw [show (KssB + 204 : Word) + 8 = KssB + 212 from by decide] at c0
  let out1 := setBytes out0 (8 * 0) ((st.drop (8 * 0)).take 8)
  have hout1 : out1.length = 32 := by simp only [out1, length_setBytes, hout0]
  have c1 := kssDigestDword_spec (KssB + 212) outputBase st out1 1
    (packBytes ((st.drop (8 * 0)).take 8)) hst hout1 (by omega)
    (kss_mem_at 53 (.LD .x5 .x19 (BitVec.ofNat 12 (8 * 1))) (KssB + 212)
      (by decide) (by rw [kssProgL_len]; decide) (by rfl))
    (by
      have h := kss_mem_at 54 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 1))) (KssB + 216)
        (by decide) (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 212 : Word) + 4 = KssB + 216 from by decide])
  rw [show (KssB + 212 : Word) + 8 = KssB + 220 from by decide] at c1
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  let out2 := setBytes out1 (8 * 1) ((st.drop (8 * 1)).take 8)
  have hout2 : out2.length = 32 := by simp only [out2, length_setBytes, hout1]
  have c2 := kssDigestDword_spec (KssB + 220) outputBase st out2 2
    (packBytes ((st.drop (8 * 1)).take 8)) hst hout2 (by omega)
    (kss_mem_at 55 (.LD .x5 .x19 (BitVec.ofNat 12 (8 * 2))) (KssB + 220)
      (by decide) (by rw [kssProgL_len]; decide) (by rfl))
    (by
      have h := kss_mem_at 56 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 2))) (KssB + 224)
        (by decide) (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 220 : Word) + 4 = KssB + 224 from by decide])
  rw [show (KssB + 220 : Word) + 8 = KssB + 228 from by decide] at c2
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  let out3 := setBytes out2 (8 * 2) ((st.drop (8 * 2)).take 8)
  have hout3 : out3.length = 32 := by simp only [out3, length_setBytes, hout2]
  have c3 := kssDigestDword_spec (KssB + 228) outputBase st out3 3
    (packBytes ((st.drop (8 * 2)).take 8)) hst hout3 (by omega)
    (kss_mem_at 57 (.LD .x5 .x19 (BitVec.ofNat 12 (8 * 3))) (KssB + 228)
      (by decide) (by rw [kssProgL_len]; decide) (by rfl))
    (by
      have h := kss_mem_at 58 (.SD .x18 .x5 (BitVec.ofNat 12 (8 * 3))) (KssB + 232)
        (by decide) (by rw [kssProgL_len]; decide) (by rfl)
      rwa [show (KssB + 228 : Word) + 4 = KssB + 232 from by decide])
  rw [show (KssB + 228 : Word) + 8 = KssB + 236 from by decide] at c3
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  refine cpsTripleWithin_weaken (fun _ hp => by simpa [out0] using hp)
    (fun hSt hq => ?_) cAll
  have hq1 :
      ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) **
        bytesRegion KssZk3 st **
        bytesRegion outputBase
          (setBytes out3 (8 * 3) ((st.drop (8 * 3)).take 8))) hSt := by
    refine (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (regIs_implies_regOwn .x5)))) _ hq
  simpa [keccakDigestCopy, out0, out1, out2, out3] using hq1

/-! ## The assembled tail -/

/-- Exposed temps that pass through the tail owned. -/
def kssTailOwns : List Reg :=
  [.x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29, .x30, .x31]

/-- Ambient carried through the tail: the sponge base, the output pointer,
    the hardwired zero register, the exposed temporaries the accelerator may
    clobber, the caller's output buffer, and the caller's free assertion. -/
def kssTailAmb (outputBase : Word) (out : List (BitVec 8)) (A : Assertion) : Assertion :=
  (.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
    regOwns kssTailOwns ** bytesRegion outputBase out ** A

theorem kssTailAmb_pcFree (outputBase : Word) (out : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) : (kssTailAmb outputBase out A).pcFree :=
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (by pcf) <|
  pcFree_sepConj (pcFree_regOwns _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- The padded-then-permuted sponge image: `pad10*1` at the carried fill
    offset, then one Keccak-f. -/
def kssFinalState (st : List (BitVec 8)) (fill : Nat) : List (BitVec 8) :=
  setBytes (keccakGuestPad st fill) 0 (keccakBytes (keccakGuestPad st fill) 0)

theorem kssFinalState_length (st : List (BitVec 8)) (fill : Nat)
    (hst : st.length = 200) : (kssFinalState st fill).length = 200 := by
  simp only [kssFinalState, keccakGuestPad, length_setBytes, hst]

/-- Reassemble `own x5 ** own x6 ** own x7 ** regOwns kssTailOwns` into
    `regOwns keccakCsrsRest` (the exact set `csrs 0x800` may clobber). -/
private theorem kssTail_assemble_csrsRest (R : Assertion) :
    ∀ h, ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
      regOwns kssTailOwns ** R) h → (regOwns keccakCsrsRest ** R) h := by
  intro h hs
  have unfolded : ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
      ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
        (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** (regOwn .x28) **
        (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) ** empAssertion) **
      R) h := by
    simpa [regOwns, kssTailOwns, regOwn] using hs
  have goal : (((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
      (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion) ** R) h := by
    xperm_hyp unfolded
  simpa [regOwns, keccakCsrsRest, regOwn] using goal

/-- Split `regOwns keccakCsrsRest` back into `own x5/x6/x7 ** regOwns kssTailOwns`. -/
private theorem kssTail_split_csrsRest (R : Assertion) :
    ∀ h, (regOwns keccakCsrsRest ** R) h →
      ((regOwn .x6) ** (regOwn .x7) ** regOwns kssTailOwns ** (regOwn .x5) ** R) h := by
  intro h hs
  have unfolded : (((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) ** (regOwn .x28) **
      (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) **
      (regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
      (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** empAssertion) ** R) h := by
    simpa [regOwns, keccakCsrsRest, regOwn] using hs
  have goal : ((regOwn .x6) ** (regOwn .x7) **
      ((regOwn .x11) ** (regOwn .x12) ** (regOwn .x13) ** (regOwn .x14) **
        (regOwn .x15) ** (regOwn .x16) ** (regOwn .x17) ** (regOwn .x28) **
        (regOwn .x29) ** (regOwn .x30) ** (regOwn .x31) ** empAssertion) **
      (regOwn .x5) ** R) h := by
    xperm_hyp unfolded
  simpa [regOwns, kssTailOwns, regOwn] using goal

/-- ⭐ **The tail of `zkvm_keccak256_segments`**: `KssB+164` → `KssB+240`.

    `st` is the sponge image at the `.Lkss_done` label and `fill` the rate-block
    fill offset live in `s4`.  In at most 20 machine steps the routine pads,
    permutes, squeezes the 32-byte digest into the caller's buffer and returns
    status `0` in `a0`.

    Both regions the tail writes are named in the pre AND the post: the 200-byte
    sponge arena (`bytesRegion KssZk3 …`) and the 32-byte output buffer, so no
    frame can own a cell the routine touches. -/
theorem kssTail_spec (outputBase : Word) (st : List (BitVec 8)) (fill : Nat)
    (A : Assertion) (hA : A.pcFree)
    (hst : st.length = 200) (hfill : fill ≤ 135)
    (halign : KssZk3.toNat % 8 = 0)
    (h_over : KssZk3.toNat + 200 ≤ 2 ^ 64)
    (hvalidFill : isValidByteAccess (KssZk3 + BitVec.ofNat 64 fill) = true)
    (hvalid135 : isValidByteAccess (KssZk3 + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (KssZk3 + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 20 (KssB + 164) (KssB + 240) kssCr
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (regOwn .x10) **
        bytesRegion KssZk3 st **
        kssTailAmb outputBase (List.replicate 32 (0 : BitVec 8)) A)
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion KssZk3 (kssFinalState st fill) **
        kssTailAmb outputBase (keccakDigestCopy (kssFinalState st fill)) A) := by
  let out0 : List (BitVec 8) := List.replicate 32 (0 : BitVec 8)
  let stPad : List (BitVec 8) := keccakGuestPad st fill
  have hstPad : stPad.length = 200 := by
    simp only [stPad, keccakGuestPad, length_setBytes, hst]
  let stFin : List (BitVec 8) := setBytes stPad 0 (keccakBytes stPad 0)
  have hstFin : stFin.length = 200 := by
    simp only [stFin, length_setBytes, hstPad]
  -- ambient carried through pad: everything except x6/x7/x19/x20 and the sponge
  let AmbPad : Assertion :=
    (.x18 ↦ᵣ outputBase) ** (.x0 ↦ᵣ (0 : Word)) **
      (regOwn .x5) ** (regOwn .x10) ** regOwns kssTailOwns **
      bytesRegion outputBase out0 ** A
  have hAmbPad : AmbPad.pcFree :=
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA
  -- ── 1. pad block (own x6/x7 peeled to values) ───────────────────────────
  have hpadCore (v6 v7 : Word) :=
    kssPadBlock_spec st fill v6 v7 hst hfill halign h_over hvalidFill hvalid135
  have hpadOwn : cpsTripleWithin 8 (KssB + 164) (KssB + 196) kssCr
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (regOwn .x6) ** (regOwn .x7) ** bytesRegion KssZk3 st)
      ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
        (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
        bytesRegion KssZk3 stPad) := by
    have h7 (v6 : Word) : cpsTripleWithin 8 (KssB + 164) (KssB + 196) kssCr
        (((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
            (.x6 ↦ᵣ v6) ** bytesRegion KssZk3 st) ** regOwn .x7)
        ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
          (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
          bytesRegion KssZk3 stPad) := by
      refine of_forall1 (fun v7 => ?_)
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by simpa [stPad] using hq) (hpadCore v6 v7)
    have h6 (v6 : Word) : cpsTripleWithin 8 (KssB + 164) (KssB + 196) kssCr
        (((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
            (regOwn .x7) ** bytesRegion KssZk3 st) ** (.x6 ↦ᵣ v6))
        ((.x19 ↦ᵣ KssZk3) ** (.x20 ↦ᵣ BitVec.ofNat 64 fill) **
          (.x6 ↦ᵣ (KssZk3 + BitVec.ofNat 64 135)) ** (regOwn .x7) **
          bytesRegion KssZk3 stPad) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (h7 v6)
    have hown := of_forall1 h6
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hown
  have hpadF := cpsTripleWithin_frameR AmbPad hAmbPad hpadOwn
  -- pad, reshaped into the flat tail ambient
  have cPad : cpsTripleWithin 8 (KssB + 164) (KssB + 196) kssCr
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (regOwn .x10) **
        bytesRegion KssZk3 st **
        kssTailAmb outputBase out0 A)
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (regOwn .x10) **
        bytesRegion KssZk3 stPad **
        kssTailAmb outputBase out0 A) := by
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hpadF
    · simp only [kssTailAmb, AmbPad] at hp ⊢; xperm_hyp hp
    · simp only [kssTailAmb, AmbPad] at hq ⊢
      have hq1 := (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (regIs_implies_regOwn .x6))))) _ hq
      xperm_hyp hq1
  -- ── 2. final CSRS ────────────────────────────────────────────────────────
  have hcsrsCore (v10 : Word) := kssFinalCsrs_spec stPad
    ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (.x18 ↦ᵣ outputBase) **
      (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outputBase out0 ** A)
    (pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (by pcf) <|
      pcFree_sepConj (bytesRegion_pcFree _ _) hA)
    hstPad halign hvalidMem v10
  -- CSRS with x5 left owned (it is re-loaded by the squeeze anyway)
  have cCsrs : cpsTripleWithin 2 (KssB + 196) (KssB + 204) kssCr
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (regOwn .x10) **
        bytesRegion KssZk3 stPad **
        kssTailAmb outputBase out0 A)
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x6) ** (regOwn .x7) **
        (regOwn .x5) ** (.x10 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 stFin **
        kssTailAmb outputBase out0 A) := by
    have hown : cpsTripleWithin 2 (KssB + 196) (KssB + 204) kssCr
        (((.x19 ↦ᵣ KssZk3) ** regOwns keccakCsrsRest **
            bytesRegion KssZk3 stPad **
            ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (.x18 ↦ᵣ outputBase) **
              (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outputBase out0 ** A)) **
          regOwn .x10)
        ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ KssZk3) **
          regOwns keccakCsrsRest **
          bytesRegion KssZk3 stFin **
          ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (.x18 ↦ᵣ outputBase) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outputBase out0 ** A)) := by
      refine of_forall1 (fun v10 => ?_)
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => by simpa [stFin] using hq) (hcsrsCore v10)
    refine cpsTripleWithin_weaken (fun hS hp => ?_) (fun hS hq => ?_) hown
    · simp only [kssTailAmb] at hp
      have hp1 : ((regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
          regOwns kssTailOwns **
          ((.x19 ↦ᵣ KssZk3) ** (regOwn .x10) **
            bytesRegion KssZk3 stPad **
            (.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (.x18 ↦ᵣ outputBase) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outputBase out0 ** A)) hS := by
        xperm_hyp hp
      have hp2 := kssTail_assemble_csrsRest _ hS hp1
      xperm_hyp hp2
    · simp only [kssTailAmb]
      have hq1 : (regOwns keccakCsrsRest **
          ((.x19 ↦ᵣ KssZk3) ** (.x10 ↦ᵣ KssZk3) **
            bytesRegion KssZk3 stFin **
            (.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (.x18 ↦ᵣ outputBase) **
            (.x0 ↦ᵣ (0 : Word)) ** bytesRegion outputBase out0 ** A)) hS := by
        xperm_hyp hq
      have hq2 := kssTail_split_csrsRest _ hS hq1
      xperm_hyp hq2
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) cPad cCsrs
  -- ── 3. squeeze ───────────────────────────────────────────────────────────
  have cDig : cpsTripleWithin 8 (KssB + 204) (KssB + 236) kssCr
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x6) ** (regOwn .x7) **
        (regOwn .x5) ** (.x10 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 stFin **
        kssTailAmb outputBase out0 A)
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x6) ** (regOwn .x7) **
        (regOwn .x5) ** (.x10 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 stFin **
        kssTailAmb outputBase (keccakDigestCopy stFin) A) := by
    have hown : cpsTripleWithin 8 (KssB + 204) (KssB + 236) kssCr
        (((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) **
            bytesRegion KssZk3 stFin ** bytesRegion outputBase out0) **
          regOwn .x5)
        ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
          bytesRegion KssZk3 stFin **
          bytesRegion outputBase (keccakDigestCopy stFin)) := by
      refine of_forall1 (fun v5 => ?_)
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (kssDigestAll_spec outputBase stFin v5 hstFin)
    have hcore : cpsTripleWithin 8 (KssB + 204) (KssB + 236) kssCr
        ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
          bytesRegion KssZk3 stFin ** bytesRegion outputBase out0)
        ((.x19 ↦ᵣ KssZk3) ** (.x18 ↦ᵣ outputBase) ** (regOwn .x5) **
          bytesRegion KssZk3 stFin **
          bytesRegion outputBase (keccakDigestCopy stFin)) := by
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hown
    have hF := cpsTripleWithin_frameR
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x6) ** (regOwn .x7) **
        (.x10 ↦ᵣ KssZk3) ** (.x0 ↦ᵣ (0 : Word)) ** regOwns kssTailOwns ** A)
      (pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (pcFree_regOwns _) hA) hcore
    refine cpsTripleWithin_weaken (fun _ hp => ?_) (fun _ hq => ?_) hF
    · simp only [kssTailAmb] at hp ⊢; xperm_hyp hp
    · simp only [kssTailAmb] at hq ⊢; xperm_hyp hq
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 cDig
  -- ── 4. LI a0, 0 ──────────────────────────────────────────────────────────
  have cLi : cpsTripleWithin 1 (KssB + 236) (KssB + 240) kssCr
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x6) ** (regOwn .x7) **
        (regOwn .x5) ** (.x10 ↦ᵣ KssZk3) **
        bytesRegion KssZk3 stFin **
        kssTailAmb outputBase (keccakDigestCopy stFin) A)
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion KssZk3 stFin **
        kssTailAmb outputBase (keccakDigestCopy stFin) A) := by
    have hli := keccakLi0_spec kssCr (KssB + 236) KssZk3
      (kss_mem_at 59 (.LI .x10 (0 : Word)) (KssB + 236) (by decide)
        (by rw [kssProgL_len]; decide) (by rfl))
    rw [show (KssB + 236 : Word) + 4 = KssB + 240 from by decide] at hli
    have hliF := cpsTripleWithin_frameR
      ((.x20 ↦ᵣ BitVec.ofNat 64 fill) ** (regOwn .x5) ** (regOwn .x6) **
        (regOwn .x7) ** bytesRegion KssZk3 stFin **
        kssTailAmb outputBase (keccakDigestCopy stFin) A)
      (pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (by pcf) <|
        pcFree_sepConj (bytesRegion_pcFree _ _)
          (kssTailAmb_pcFree _ _ _ hA)) hli
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hliF
  have cAll := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 cLi
  have cFinal := cpsTripleWithin_weaken (fun _ hp => by simpa [out0] using hp)
    (fun _ hq => by simpa [kssFinalState, stPad, stFin] using hq) cAll
  exact cpsTripleWithin_mono_nSteps (by omega) cFinal

end EvmAsm.Codegen.Proofs
