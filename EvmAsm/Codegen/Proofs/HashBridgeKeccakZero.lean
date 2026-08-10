/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakZero

  Zero-state countdown for the inline `zkvm_keccak256` wrapper:
  25 dword stores of x0 through an advancing cursor, bottom-tested by
  BNE x29,x0,-12.  Pattern mirrors `ZeroPadLoop` (byte SB) with dword SD.
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakPure
import EvmAsm.Rv64.SAsm.AbiFrameLoopBottom
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.SelectedRead
import EvmAsm.Rv64.MemRegionWriteWide

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000

/-- `SD rs2, 0(rs1)` through an advancing cursor writes dword chunk `q`
    when `rs1 = base + 8q` — cursor analogue of `bytesRegion_sd_within`. -/
theorem bytesRegion_sd_cursor_within (rs1 rs2 : Reg) (regionBase v_data : Word)
    (base : Word) (bs : List (BitVec 8)) (q : Nat)
    (hq : 8 * q + 8 ≤ bs.length) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.SD rs1 rs2 (0 : BitVec 12)))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q))) ** (rs2 ↦ᵣ v_data) **
        bytesRegion regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 (8 * q))) ** (rs2 ↦ᵣ v_data) **
        bytesRegion regionBase (setBytes bs (8 * q) (dwordBytes v_data))) := by
  obtain ⟨front, rest, hf, hr, heq, heqset⟩ :=
    bytesRegion_dword_at_setBytes regionBase bs (dwordBytes v_data) q 0
      (by simp [dwordBytes]) (by simp) (by simp only [length_dwordBytes]; omega)
  have hsd := sd_spec_gen_within rs1 rs2
    (regionBase + BitVec.ofNat 64 (8 * q)) v_data
    (packBytes ((bs.drop (8 * q)).take 8)) (0 : BitVec 12) base
  rw [show (regionBase + BitVec.ofNat 64 (8 * q)) + signExtend12 (0 : BitVec 12)
      = regionBase + BitVec.ofNat 64 (8 * q) from by
    rw [signExtend12_0]
    bv_omega] at hsd
  have hchunk : packBytes (setBytes ((bs.drop (8 * q)).take 8) 0 (dwordBytes v_data))
      = v_data :=
    (packBytes_setBytes_dword ((bs.drop (8 * q)).take 8) v_data
      (by rw [List.length_take, List.length_drop]; omega)).symm
  rw [show (8 * q + 0 : Nat) = 8 * q from by omega, hchunk] at heqset
  rw [heq, heqset]
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hq' => by xperm_hyp hq')
    (cpsTripleWithin_frameR (front ** rest) (pcFree_sepConj hf hr) hsd)

private theorem dwordBytes_zero' :
    dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) := by
  simp only [dwordBytes, extractByte]
  rfl

/-- Writing the next zero dword extends the zeroed prefix by 8 bytes. -/
private theorem zero_dword_set (os : List (BitVec 8)) (k : Nat)
    (hk : 8 * k + 8 ≤ os.length) :
    setBytes (List.replicate (8 * k) (0 : BitVec 8) ++ os.drop (8 * k))
        (8 * k) (dwordBytes (0 : Word))
      = List.replicate (8 * (k + 1)) (0 : BitVec 8) ++ os.drop (8 * (k + 1)) := by
  rw [dwordBytes_zero']
  have hleft :
      setBytes (List.replicate (8 * k) (0 : BitVec 8) ++ os.drop (8 * k))
          (8 * k) (List.replicate 8 (0 : BitVec 8))
        = List.replicate (8 * k) (0 : BitVec 8) ++
            setBytes (os.drop (8 * k)) 0 (List.replicate 8 (0 : BitVec 8)) := by
    rw [setBytes_append_right _ _ _ _ (by simp [List.length_replicate])]
    simp only [List.length_replicate, Nat.sub_self]
  rw [hleft]
  have htail :
      setBytes (os.drop (8 * k)) 0 (List.replicate 8 (0 : BitVec 8))
        = List.replicate 8 (0 : BitVec 8) ++ os.drop (8 * (k + 1)) := by
    have hdrop : 8 ≤ (os.drop (8 * k)).length := by
      rw [List.length_drop]; omega
    have hfull :
        setBytes ((os.drop (8 * k)).take 8) 0 (List.replicate 8 (0 : BitVec 8))
          = List.replicate 8 (0 : BitVec 8) := by
      have h := setBytes_dword_full ((os.drop (8 * k)).take 8) (0 : Word)
        (by rw [List.length_take]; omega)
      rwa [dwordBytes_zero'] at h
    have hsplit :
        setBytes (os.drop (8 * k)) 0 (List.replicate 8 (0 : BitVec 8))
          = setBytes ((os.drop (8 * k)).take 8) 0 (List.replicate 8 (0 : BitVec 8))
              ++ (os.drop (8 * k)).drop 8 := by
      have heq : os.drop (8 * k)
          = (os.drop (8 * k)).take 8 ++ (os.drop (8 * k)).drop 8 :=
        (List.take_append_drop 8 (os.drop (8 * k))).symm
      conv_lhs => rw [heq]
      rw [setBytes_append_left _ _ _ _
        (by simp only [List.length_take, List.length_replicate]; omega)]
    rw [hsplit, hfull, List.drop_drop]
    simp only [Nat.mul_add, Nat.mul_one]
  rw [htail, ← List.append_assoc, ← List.replicate_add]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem cursor_advance8 (p : Word) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + signExtend12 (8 : BitVec 12)
      = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show ((8 : Word)).toNat = 8 from rfl,
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

/-- Invariant at remaining dword count `n`: `25 - n` dwords zeroed,
    cursor past them. -/
def keccakZeroInv (cur : Reg) (dst : Word) (os : List (BitVec 8))
    (n : Nat) : Assertion :=
  (cur ↦ᵣ (dst + BitVec.ofNat 64 (8 * (25 - n)))) **
  bytesRegion dst
    (List.replicate (8 * (25 - n)) (0 : BitVec 8) ++ os.drop (8 * (25 - n)))

/-- Whole zero-state countdown: 25 dword stores of x0 through an advancing
    cursor, bottom-tested by `BNE ctr,x0,-12`.  Exits with the 200-byte
    region fully zeroed and the cursor at `dst + 200`. -/
theorem keccakZeroLoop_spec (cr : CodeReq) (hdr : Word) (cur ctr : Reg)
    (dst : Word) (os : List (BitVec 8))
    (hcur : cur ≠ .x0) (hctr : ctr ≠ .x0)
    (hlen : os.length = 200)
    (halignD : dst.toNat % 8 = 0) (hover : dst.toNat + 200 < 2 ^ 64)
    (hmemSd : ∀ a i, CodeReq.singleton hdr (.SD cur .x0 0) a = some i →
      cr a = some i)
    (hmemA1 : ∀ a i,
      CodeReq.singleton (hdr + 4) (.ADDI cur cur (8 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemA2 : ∀ a i,
      CodeReq.singleton (hdr + 8) (.ADDI ctr ctr (-1 : BitVec 12)) a = some i →
      cr a = some i)
    (hmemBne : ∀ a i,
      CodeReq.singleton (hdr + 12) (.BNE ctr .x0 (-12 : BitVec 13)) a = some i →
      cr a = some i) :
    cpsTripleWithin (25 * 4) hdr (hdr + 16) cr
      ((cur ↦ᵣ dst) ** (ctr ↦ᵣ BitVec.ofNat 64 25) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion dst os)
      ((cur ↦ᵣ (dst + BitVec.ofNat 64 200)) ** (ctr ↦ᵣ BitVec.ofNat 64 0) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion dst keccakZeroStateBytes) := by
  have hbody : ∀ n, n < 25 →
      cpsTripleWithin 3 hdr (hdr + 12) cr
        ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** keccakZeroInv cur dst os (n + 1))
        ((ctr ↦ᵣ BitVec.ofNat 64 n) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word))
          ** keccakZeroInv cur dst os n) := by
    intro n hn
    set k := 25 - (n + 1) with hk
    have hkN : k < 25 := by omega
    have hq : 8 * k + 8 ≤
        (List.replicate (8 * k) (0 : BitVec 8) ++ os.drop (8 * k)).length := by
      simp only [List.length_append, List.length_replicate, List.length_drop, hlen]
      omega
    have hsd := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemSd)
      (h := bytesRegion_sd_cursor_within cur .x0 dst (0 : Word) hdr
        (List.replicate (8 * k) (0 : BitVec 8) ++ os.drop (8 * k)) k hq)
    rw [zero_dword_set os k (by omega)] at hsd
    have ha1 := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemA1)
      (h := addi_spec_gen_same_within cur (dst + BitVec.ofNat 64 (8 * k))
        (8 : BitVec 12) (hdr + 4) hcur)
    rw [cursor_advance8 dst k,
        show hdr + 4 + 4 = hdr + 8 from by
          rw [BitVec.add_assoc,
            show ((4 : Word) + 4) = (8 : Word) from by decide]] at ha1
    have ha2 := cpsTripleWithin_extend_code (cr' := cr) (hmono := hmemA2)
      (h := addi_spec_gen_same_within ctr (BitVec.ofNat 64 (n + 1))
        (-1 : BitVec 12) (hdr + 8) hctr)
    rw [ctr_dec n (by omega),
        show hdr + 8 + 4 = hdr + 12 from by
          rw [BitVec.add_assoc,
            show ((8 : Word) + 4) = (12 : Word) from by decide]] at ha2
    have hsdF := cpsTripleWithin_frameR
      ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)))
      pcFree_regIs hsd
    have ha1F := cpsTripleWithin_frameR
      ((ctr ↦ᵣ BitVec.ofNat 64 (n + 1)) ** ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion dst
          (List.replicate (8 * (k + 1)) (0 : BitVec 8) ++ os.drop (8 * (k + 1))))
      (by pcf) ha1
    have ha2F := cpsTripleWithin_frameR
      ((cur ↦ᵣ (dst + BitVec.ofNat 64 (8 * (k + 1)))) **
        ((Reg.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion dst
          (List.replicate (8 * (k + 1)) (0 : BitVec 8) ++ os.drop (8 * (k + 1))))
      (by pcf) ha2
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hsdF ha1F
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hc1 ha2F
    refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hc2
    · unfold keccakZeroInv at hp
      rw [← hk] at hp
      xperm_hyp hp
    · unfold keccakZeroInv
      rw [show 25 - n = k + 1 from by omega]
      xperm_hyp hq
  have hloop := countdownLoopBottom_spec cr hdr (hdr + 12) ctr
    (-12 : BitVec 13) 3 25 (keccakZeroInv cur dst os) hctr (by decide) (by decide)
    (by
      rw [show signExtend13 (-12 : BitVec 13) = (-12 : Word) from by decide]
      bv_omega)
    (fun n => by unfold keccakZeroInv; pcf)
    hmemBne
    hbody
  rw [show hdr + 12 + 4 = hdr + 16 from by
    rw [BitVec.add_assoc,
      show ((12 : Word) + 4) = (16 : Word) from by decide]] at hloop
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_)
    (cpsTripleWithin_mono_nSteps (by omega) hloop)
  · unfold keccakZeroInv
    rw [show 25 - 25 = 0 from by omega,
        show dst + BitVec.ofNat 64 (8 * 0) = dst from by
          rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
          bv_omega,
        show (List.replicate (8 * 0) (0 : BitVec 8) ++ os.drop (8 * 0)) = os from by
          simp]
    xperm_hyp hp
  · unfold keccakZeroInv at hq
    rw [show 25 - 0 = 25 from by omega,
        show 8 * 25 = 200 from by decide,
        show os.drop 200 = [] from by
          apply List.drop_eq_nil_of_le
          omega,
        List.append_nil] at hq
    simp only [keccakZeroStateBytes] at hq ⊢
    xperm_hyp hq

end EvmAsm.Codegen.Proofs
