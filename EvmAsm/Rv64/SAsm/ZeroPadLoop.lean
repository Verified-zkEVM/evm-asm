/-
  EvmAsm.Rv64.SAsm.ZeroPadLoop

  The **reusable zero-pad countdown loop** and the nested-loop-in-count-up
  template (bead evm-asm-db2jq).

  Wire-format encoders (`blsk_g2_wire`, `blsk_g1_wire`) zero-pad each
  output record with an embedded byte-store countdown INSIDE the outer
  count-up call loop:

  ```
        li   ctr, N
  hdr:  sb   x0, 0(cur)
        addi cur, cur, 1
        addi ctr, ctr, -1
        bne  ctr, x0, hdr          -- bottom-tested countdown
  ```

  `zeroPadLoop_spec` proves the whole pad ONCE, register-, length- and
  base-agnostic: from the cursor at `dst` and the counter at `N`, the
  loop exits with the `N`-byte region ZEROED (`List.replicate N 0` —
  the genuine post, not a per-byte residue) and the cursor at `dst + N`.
  It is a `countdownLoopBottom_spec` instance whose invariant carries the
  written prefix as `replicate k 0 ++ os.drop k`.

  **The nested-loop-in-count-up template** (what makes `blsk_g2_wire`
  compose): `countupLoopBottom_spec`'s per-iteration hypothesis is an
  ordinary `cpsTripleWithin` over the body — the body being itself a
  loop (this pad), a cross-call (`callWithin_spec` on an adapter-derived
  contract), or both, changes nothing: prove the inner loop's triple
  with THIS lemma, `cpsTripleWithin_seq_perm_same_cr` it between the
  surrounding straight-line segments, and hand the composite to the
  outer loop exactly as a straight-line body would be.  No new outer
  machinery is needed — the consumer
  (`Codegen/Programs/Bls12KzgG2WireSAsm.lean`) is the worked example.

  Everything additive, `cpsTripleWithin` level.
-/

import EvmAsm.Rv64.SAsm.AbiFrameLoopBottom
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

namespace ZeroPadLoop

/-- Writing the next zero byte extends the zeroed prefix. -/
private theorem pad_set (os : List (BitVec 8)) (k : Nat) (hk : k < os.length) :
    (List.replicate k (0 : BitVec 8) ++ os.drop k).set k (0 : BitVec 8)
      = List.replicate (k + 1) (0 : BitVec 8) ++ os.drop (k + 1) := by
  apply List.ext_getElem
  · simp only [List.length_set, List.length_append, List.length_replicate,
      List.length_drop]
    omega
  · intro j hj1 hj2
    simp only [List.length_set, List.length_append, List.length_replicate,
      List.length_drop] at hj1 hj2
    by_cases hjk : j = k
    · subst hjk
      rw [List.getElem_set_self]
      rw [List.getElem_append_left (by simp only [List.length_replicate]; omega)]
      simp
    · rw [List.getElem_set_ne (by omega)]
      by_cases hjlt : j < k
      · rw [List.getElem_append_left (by simp only [List.length_replicate]; omega),
          List.getElem_append_left (by simp only [List.length_replicate]; omega)]
        simp
      · have hjgt : k < j := by omega
        rw [List.getElem_append_right (by simp only [List.length_replicate]; omega),
          List.getElem_append_right (by simp only [List.length_replicate]; omega)]
        simp only [List.length_replicate, List.getElem_drop]
        congr 1
        omega

private theorem cursor_advance (p : Word) (k : Nat) :
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

/-- The pad-loop invariant at remaining count `n`: `N - n` bytes written,
    the cursor past them, the region = zeroed prefix + untouched tail. -/
def padInv (cur : Reg) (dst : Word) (os : List (BitVec 8)) (N : Nat)
    (n : Nat) : Assertion :=
  (cur ↦ᵣ (dst + BitVec.ofNat 64 (N - n))) **
  bytesRegion dst
    (List.replicate (N - n) (0 : BitVec 8) ++ os.drop (N - n))

/-- **The zero-pad countdown loop, whole-loop**: from the cursor at `dst`
    and the counter at `N ≥ 1`, the `sb/addi/addi/bne` countdown exits
    with the `N`-byte region ZEROED and the cursor at `dst + N`.
    Register-, length- and base-agnostic; the four instruction addresses
    are `hdr`, `hdr+4`, `hdr+8`, `hdr+12` with membership hypotheses the
    consumer discharges (`code_mem` at concrete bases). -/
theorem zeroPadLoop_spec (cr : CodeReq) (hdr : Word) (cur ctr : Reg)
    (dst : Word) (os : List (BitVec 8)) (N : Nat)
    (hcur : cur ≠ .x0) (hctr : ctr ≠ .x0)
    (hN1 : 1 ≤ N) (hlen : os.length = N)
    (halignD : dst.toNat % 8 = 0) (hover : dst.toNat + N < 2 ^ 64)
    (hvalid : ∀ k, k < N → isValidByteAccess (dst + BitVec.ofNat 64 k) = true)
    (hmemSb : ∀ a i, CodeReq.singleton hdr (.SB cur .x0 0) a = some i →
      cr a = some i)
    (hmemA1 : ∀ a i,
      CodeReq.singleton (hdr + 4) (.ADDI cur cur (1 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemA2 : ∀ a i,
      CodeReq.singleton (hdr + 8) (.ADDI ctr ctr (-1 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i,
      CodeReq.singleton (hdr + 12) (.BNE ctr .x0 (-12 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin (N * 4) hdr (hdr + 16) cr
      ((cur ↦ᵣ dst) ** (ctr ↦ᵣ BitVec.ofNat 64 N) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion dst os)
      ((cur ↦ᵣ (dst + BitVec.ofNat 64 N)) ** (ctr ↦ᵣ BitVec.ofNat 64 0) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion dst (List.replicate N (0 : BitVec 8))) := by
  have hNlt : N < 2 ^ 64 := by omega
  -- the per-iteration body: SB ; ADDI cur ; ADDI ctr
  have hbody : ∀ n, n < N →
      cpsTripleWithin 3 hdr (hdr + 12) cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** padInv cur dst os N (n + 1))
        ((ctr ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** padInv cur dst os N n) := by
    intro n hn
    set k := N - (n + 1) with hk
    have hkN : k < N := by omega
    have hkos : k < os.length := by omega
    have hlenPad : (List.replicate k (0 : BitVec 8) ++ os.drop k).length
        = os.length := by
      simp only [List.length_append, List.length_replicate, List.length_drop]
      omega
    -- sb x0, 0(cur)
    have hsb := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemSb)
      (h := bytesRegion_sb_within cur .x0 dst (0 : Word) hdr
        (List.replicate k (0 : BitVec 8) ++ os.drop k) k
        halignD (by omega) (by omega) (hvalid k hkN))
    rw [show ((0 : Word)).truncate 8 = (0 : BitVec 8) from by decide,
        pad_set os k hkos] at hsb
    -- addi cur, cur, 1
    have ha1 := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemA1)
      (h := addi_spec_gen_same_within cur (dst + BitVec.ofNat 64 k)
        (1 : BitVec 12) (hdr + 4) hcur)
    rw [cursor_advance dst k,
        show hdr + 4 + 4 = hdr + 8 from by
          rw [BitVec.add_assoc,
            show ((4 : Word) + 4) = (8 : Word) from by decide]] at ha1
    -- addi ctr, ctr, -1
    have ha2 := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemA2)
      (h := addi_spec_gen_same_within ctr (BitVec.ofNat 64 (n + 1))
        (-1 : BitVec 12) (hdr + 8) hctr)
    rw [ctr_dec n (by omega),
        show hdr + 8 + 4 = hdr + 12 from by
          rw [BitVec.add_assoc,
            show ((8 : Word) + 4) = (12 : Word) from by decide]] at ha2
    -- frames + chain
    have hsbF := cpsTripleWithin_frameR
      ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)))
      pcFree_regIs hsb
    have ha1F := cpsTripleWithin_frameR
      ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion dst
          (List.replicate (k + 1) (0 : BitVec 8) ++ os.drop (k + 1)))
      (by pcf) ha1
    have ha2F := cpsTripleWithin_frameR
      ((cur ↦ᵣ (dst + BitVec.ofNat 64 (k + 1))) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion dst
          (List.replicate (k + 1) (0 : BitVec 8) ++ os.drop (k + 1)))
      (by pcf) ha2
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hsbF ha1F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hc1 ha2F
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hc2
    · unfold padInv at hp
      rw [← hk] at hp
      xperm_hyp hp
    · unfold padInv
      rw [show N - n = k + 1 from by omega]
      xperm_hyp hq
  have hloop := countdownLoopBottom_spec cr hdr (hdr + 12) ctr
    (-12 : BitVec 13) 3 N (padInv cur dst os N) hctr hN1 (by omega)
    (by
      rw [show signExtend13 (-12 : BitVec 13) = (-12 : Word) from by decide]
      bv_omega)
    (fun n => by unfold padInv; pcf)
    hmemBne
    hbody
  rw [show hdr + 12 + 4 = hdr + 16 from by
    rw [BitVec.add_assoc,
      show ((12 : Word) + 4) = (16 : Word) from by decide]] at hloop
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) hloop)
  · unfold padInv
    rw [show N - N = 0 from by omega,
        show dst + BitVec.ofNat 64 0 = dst from by
          rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
          bv_omega,
        show (List.replicate 0 (0 : BitVec 8) ++ os.drop 0) = os from by
          simp]
    xperm_hyp hp
  · unfold padInv at hq
    rw [show N - 0 = N from by omega,
        show os.drop N = [] from by
          apply List.drop_eq_nil_of_le
          omega,
        List.append_nil] at hq
    xperm_hyp hq

#print axioms zeroPadLoop_spec

end ZeroPadLoop

end EvmAsm.Rv64.SAsm
