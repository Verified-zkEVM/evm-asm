/-
  EvmAsm.Rv64.RLP.UnifiedFieldScalarRead

  EL.3 / Phase 5 — leaf-field SCALAR VALUE read. Given a decoded RLP `.bytes`
  field's payload pointer (`x13`) and length (`x11`) — the register convention the
  single-item decoder leaves behind — this reads the `n` payload bytes big-endian
  and computes `x11 = Nat.fromBytesBE (payload)`, advancing `x13` to the next field.
  The missing value-extraction step for the fixed-schema STF header/tx decoders.

  Reuses the Phase-2 big-endian region loop (`rlp_phase2_long_loop_region_n_spec_within`);
  the only new code is a 2-instruction impedance-match glue (move the length from
  `x11` to the loop's count register `x14`, and zero the accumulator `x11`).

  Layout (program base `base`; aligned `regionBase`, buffer `bs`, payload offset `off`):
      base       ADDI x14, x11, 0     ; x14 := payload length (count)
      base+4     ADDI x11, x0, 0      ; x11 := 0 (BE accumulator)
      base+8     < 6-instr BE loop, n iterations >   (base+8 .. base+32)
      base+32    (exit)
-/

import EvmAsm.Rv64.RLP.Phase2LongLoopRegion
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.XPermPure

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.EL.RLP
open EvmAsm.Rv64.Tactics

/-- **Leaf-field scalar value read.** From the single-item decoder's output
    convention — `x13 = regionBase + ofNat off` (payload pointer), `x11 = ofNat n`
    (payload length, `1 ≤ n ≤ 8`) — the program reads the `n` payload bytes
    big-endian into `x11 = Nat.fromBytesBE ((bs.drop off).take n)` (the field's
    scalar value) and advances `x13` to `off + n` (the next field). -/
theorem unified_field_scalar_read
    (base regionBase : Word) (bs : List Byte) (off n : Nat) (v12Old v14Old : Word)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (halign : regionBase.toNat % 8 = 0)
    (hover : regionBase.toNat + bs.length < 2 ^ 64)
    (hwin : ∀ i, i < n →
        off + i < bs.length
        ∧ isValidByteAccess (regionBase + BitVec.ofNat 64 (off + i)) = true) :
    cpsTripleWithin (2 + 6 * n) base (base + 32)
      (((CodeReq.singleton base (.ADDI .x14 .x11 0)).union
          (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0))).union
          (CodeReq.ofProg (base + 8) (rlp_phase2_long_loop_body_prog (-20))))
      ((.x11 ↦ᵣ BitVec.ofNat 64 n) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ v14Old) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion regionBase bs)
      ((.x11 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE ((bs.drop off).take n))) **
       (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 (off + n))) ** (.x14 ↦ᵣ (0 : Word)) **
       (.x12 ↦ᵣ (bs.getD (off + (n - 1)) 0).zeroExtend 64) ** (.x0 ↦ᵣ (0 : Word)) **
       bytesRegion regionBase bs) := by
  -- s_mv : ADDI x14, x11, 0  — copy the length into the loop's count register
  have mv_raw := addi_spec_gen_within .x14 .x11 v14Old (BitVec.ofNat 64 n) 0 base (by decide)
  rw [show (BitVec.ofNat 64 n) + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 n from by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at mv_raw
  have s_mv : cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.ADDI .x14 .x11 0))
      ((.x11 ↦ᵣ BitVec.ofNat 64 n) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ v14Old) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0:Word)) ** bytesRegion regionBase bs)
      ((.x11 ↦ᵣ BitVec.ofNat 64 n) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0:Word)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x12 ↦ᵣ v12Old) **
         (.x0 ↦ᵣ (0:Word)) ** bytesRegion regionBase bs)
        (by pcFree) mv_raw)
  -- s_li : ADDI x11, x0, 0  — zero the big-endian accumulator
  have li_raw := addi_x0_spec_gen_within .x11 (BitVec.ofNat 64 n) 0 (base + 4) (by decide)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide] at li_raw
  have s_li : cpsTripleWithin 1 (base + 4) (base + 4 + 4)
      (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0))
      ((.x11 ↦ᵣ BitVec.ofNat 64 n) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0:Word)) ** bytesRegion regionBase bs)
      ((.x11 ↦ᵣ (0:Word)) ** (.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) **
       (.x14 ↦ᵣ BitVec.ofNat 64 n) ** (.x12 ↦ᵣ v12Old) ** (.x0 ↦ᵣ (0:Word)) ** bytesRegion regionBase bs) :=
    cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)
      (cpsTripleWithin_frameR
        ((.x13 ↦ᵣ (regionBase + BitVec.ofNat 64 off)) ** (.x14 ↦ᵣ BitVec.ofNat 64 n) **
         (.x12 ↦ᵣ v12Old) ** bytesRegion regionBase bs)
        (by pcFree) li_raw)
  rw [show base + 4 + 4 = base + 8 from by bv_omega] at s_li
  have t_glue := cpsTripleWithin_seq (CodeReq.Disjoint.singleton (by bv_omega)) s_mv s_li
  -- t_loop : the big-endian read loop
  have hback : (base + 8 + 20) + signExtend13 (-20 : BitVec 13) = base + 8 := by
    rw [show signExtend13 (-20 : BitVec 13) = (-20 : Word) from by decide]; bv_omega
  have t_loop := rlp_phase2_long_loop_region_n_spec_within n hn1 hn8 regionBase v12Old off bs
    (base + 8) (-20) halign hover hwin hback
  have hd : (((CodeReq.singleton base (.ADDI .x14 .x11 0)).union
        (CodeReq.singleton (base + 4) (.ADDI .x11 .x0 0)))).Disjoint
      (CodeReq.ofProg (base + 8) (rlp_phase2_long_loop_body_prog (-20))) :=
    CodeReq.Disjoint.union_left
      (CodeReq.Disjoint.singleton_ofProg
        (CodeReq.ofProg_none_range_len (base + 8) (rlp_phase2_long_loop_body_prog (-20)) 6 base
          (by rfl) (by intro k hk; bv_omega)))
      (CodeReq.Disjoint.singleton_ofProg
        (CodeReq.ofProg_none_range_len (base + 8) (rlp_phase2_long_loop_body_prog (-20)) 6 (base + 4)
          (by rfl) (by intro k hk; bv_omega)))
  have composed := cpsTripleWithin_seq hd t_glue t_loop
  rw [show base + 8 + 24 = base + 32 from by bv_omega,
      show (1 + 1) + 6 * n = 2 + 6 * n from by ring] at composed
  exact composed

-- Concrete cross-check: read the 3-byte scalar `[0x01, 0x02, 0x03]` at offset 0 of
-- the buffer `[0x01, 0x02, 0x03]` from `0x2000` ⇒ `x11 = 0x010203 = fromBytesBE [1,2,3]`.
example :=
  unified_field_scalar_read (0x1000 : Word) (0x2000 : Word)
    [(0x01 : Byte), (0x02 : Byte), (0x03 : Byte)] 0 3 0 0
    (by decide) (by decide) (by decide) (by decide)
    (by intro i hi; interval_cases i <;> exact ⟨by decide, by decide⟩)

end EvmAsm.Rv64.RLP
