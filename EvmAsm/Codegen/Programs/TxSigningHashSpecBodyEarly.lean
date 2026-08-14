/-
  EvmAsm.Codegen.Programs.TxSigningHashSpecBodyEarly

  Body phases for K145 `tx_signing_hash`: setup through post-nth BNE.
-/

import EvmAsm.Codegen.Programs.TxSigningHashSpecCore

namespace EvmAsm.Codegen.TxSigningHashSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen
open EvmAsm.Codegen.TxSigningHashResidual
open EvmAsm.Codegen.Proofs
open EvmAsm.Stateless.SpecRef
open EvmAsm.Rv64.Tactics

/-! ## Body entry and setup moves (body indices 0–4)

    Body entry is `H + 4·(1+|frame|) = H+36`. The first five instructions
    save `a0..a4` into `s0..s4` (`x8,x9,x18,x19,x20`). -/

abbrev tshBodyEntry : Word := H + BitVec.ofNat 64 (4 * (1 + tshFrame.length))
abbrev tshBodyExit : Word :=
  H + BitVec.ofNat 64 (4 * (1 + tshFrame.length + tshBody.length))

theorem tshBodyEntry_eq : tshBodyEntry = H + 36 := by
  unfold tshBodyEntry; rw [tshFrame_length]; decide

theorem tshBodyExit_eq : tshBodyExit = H + 332 := by
  unfold tshBodyExit; rw [tshFrame_length]; decide

/-- Five ABI moves: `s0:=a0 … s4:=a4`. `H+36 → H+56`. -/
theorem tshSetupMoves_spec
    (a0 a1 a2 a3 a4 v8 v9 v18 v19 v20 : Word) :
    cpsTripleWithin 5 (H + 36) (H + 56) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4)) := by
  -- MV x8, x10  (prog idx 9)
  have h0 := mv_spec_gen_within .x8 .x10 a0 v8 (H + 36) (by decide)
  rw [show (H + 36 : Word) + 4 = H + 40 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 36) 9 (.MV .x8 .x10)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have c0 : cpsTripleWithin 1 (H + 36) (H + 40) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20)) := by
    have hF := cpsTripleWithin_frameR
      ((.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ a4) **
        (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20))
      (by pcf) l0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  -- MV x9, x11  (prog idx 10)
  have h1 := mv_spec_gen_within .x9 .x11 a1 v9 (H + 40) (by decide)
  rw [show (H + 40 : Word) + 4 = H + 44 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 40) 10 (.MV .x9 .x11)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h1
  have c1 : cpsTripleWithin 1 (H + 40) (H + 44) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20))
      (by pcf) l1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  -- MV x18, x12  (prog idx 11)
  have h2 := mv_spec_gen_within .x18 .x12 a2 v18 (H + 44) (by decide)
  rw [show (H + 44 : Word) + 4 = H + 48 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 44) 11 (.MV .x18 .x12)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h2
  have c2 : cpsTripleWithin 1 (H + 44) (H + 48) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x13 ↦ᵣ a3) ** (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20))
      (by pcf) l2
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2
  -- MV x19, x13  (prog idx 12)
  have h3 := mv_spec_gen_within .x19 .x13 a3 v19 (H + 48) (by decide)
  rw [show (H + 48 : Word) + 4 = H + 52 from by decide] at h3
  have l3 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 48) 12 (.MV .x19 .x13)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h3
  have c3 : cpsTripleWithin 1 (H + 48) (H + 52) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ v20)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x20 ↦ᵣ v20))
      (by pcf) l3
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c012 c3
  -- MV x20, x14  (prog idx 13)
  have h4 := mv_spec_gen_within .x20 .x14 a4 v20 (H + 52) (by decide)
  rw [show (H + 52 : Word) + 4 = H + 56 from by decide] at h4
  have l4 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 52) 13 (.MV .x20 .x14)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h4
  have c4 : cpsTripleWithin 1 (H + 52) (H + 56) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4)) := by
    have hF := cpsTripleWithin_frameR
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3))
      (by pcf) l4
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0123 c4

theorem tshSetupMoves_spec_bodyEntry
    (a0 a1 a2 a3 a4 v8 v9 v18 v19 v20 : Word) :
    cpsTripleWithin 5 tshBodyEntry (tshBodyEntry + 20) fullCode
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20))
      ((.x10 ↦ᵣ a0) ** (.x11 ↦ᵣ a1) ** (.x12 ↦ᵣ a2) ** (.x13 ↦ᵣ a3) **
        (.x14 ↦ᵣ a4) **
        (.x8 ↦ᵣ a0) ** (.x9 ↦ᵣ a1) ** (.x18 ↦ᵣ a2) ** (.x19 ↦ᵣ a3) **
        (.x20 ↦ᵣ a4)) := by
  have h := tshSetupMoves_spec a0 a1 a2 a3 a4 v8 v9 v18 v19 v20
  simp only [tshBodyEntry_eq, show (H + 36 : Word) + 20 = H + 56 from by decide] at h ⊢
  exact h

/-! ## Body: `la t0, tsh_buf` then store type-prefix byte (`H+56 → H+68`) -/

theorem tsh_la_buf_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56) =
      Rv64.laHi (H + 56) TshBuf := by
  decide

theorem tsh_la_buf_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 56) =
      Rv64.laLo (H + 56) TshBuf := by
  decide

theorem tsh_la_buf_range : laInRange (H + 56) TshBuf := by
  decide

/-- `la t0, tsh_buf` at body offset 5. `H+56 → H+64`. -/
theorem tshSetupLa_spec (v5 : Word) :
    cpsTripleWithin 2 (H + 56) (H + 64) fullCode
      (.x5 ↦ᵣ v5) (.x5 ↦ᵣ TshBuf) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 56)
        (.AUIPC .x5 (Rv64.laHi (H + 56) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 56) 14
      (.AUIPC .x5 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 56)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_buf_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 56) + 4)
        (.ADDI .x5 .x5 (Rv64.laLo (H + 56) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 60) 15
      (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 56)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 56 : Word) + 4 = H + 60 := by decide
    rw [hpc, ← tsh_la_buf_lo] at hi
    exact hmem a i hi
  have h := la_materialize_within .x5 v5 (H + 56) TshBuf
    (by decide) tsh_la_buf_range hau had
  rwa [show (H + 56 : Word) + 8 = H + 64 from by decide] at h

/-- `sb t0, 0(s3)` — write type-prefix low byte into `tsh_buf[0]`.
    `H+64 → H+68`. Owns the containing dword at `TshBuf`. -/
theorem tshSetupSbType_spec (typePrefix wordOld : Word)
    (halign : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true) :
    cpsTripleWithin 1 (H + 64) (H + 68) fullCode
      ((.x5 ↦ᵣ TshBuf) ** (.x19 ↦ᵣ typePrefix) ** (TshBuf ↦ₘ wordOld))
      ((.x5 ↦ᵣ TshBuf) ** (.x19 ↦ᵣ typePrefix) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf)
          (typePrefix.truncate 8))) := by
  have h0 := sb_spec_gen_within .x5 .x19 TshBuf typePrefix (0 : BitVec 12)
    (H + 64) TshBuf wordOld
    (by
      have : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      simp only [this]; exact halign)
    (by
      have : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
      simp only [this]; exact hvalid)
  rw [show (H + 64 : Word) + 4 = H + 68 from by decide,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (TshBuf + 0 : Word) = TshBuf from by bv_omega] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 64) 16
      (.SB .x5 .x19 (0 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- Combined setup la+sb: `H+56 → H+68`. -/
theorem tshSetupLaSb_spec (v5 typePrefix wordOld : Word)
    (halign : alignToDword TshBuf = TshBuf)
    (hvalid : isValidByteAccess TshBuf = true) :
    cpsTripleWithin 3 (H + 56) (H + 68) fullCode
      ((.x5 ↦ᵣ v5) ** (.x19 ↦ᵣ typePrefix) ** (TshBuf ↦ₘ wordOld))
      ((.x5 ↦ᵣ TshBuf) ** (.x19 ↦ᵣ typePrefix) **
        (TshBuf ↦ₘ replaceByte wordOld (byteOffset TshBuf)
          (typePrefix.truncate 8))) := by
  have hla := tshSetupLa_spec v5
  have hlaF := cpsTripleWithin_frameR
    ((.x19 ↦ᵣ typePrefix) ** (TshBuf ↦ₘ wordOld)) (by pcf) hla
  have hsb := tshSetupSbType_spec typePrefix wordOld halign hvalid
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hlaF hsb

/-! ## Body: empty-length `beq s1, x0` (`H+68`)

    Taken jumps to the fail `li a0, 1` at `H+328`. Not-taken falls through to
    the list-header parse at `H+72`. -/

abbrev tshEmptyLenBeqOff : BitVec 13 := (260 : BitVec 13)
abbrev tshFailLiPC : Word := H + 328

theorem tshEmptyLenBeq_taken_pc :
    (H + 68) + signExtend13 tshEmptyLenBeqOff = tshFailLiPC := by
  unfold tshEmptyLenBeqOff tshFailLiPC H; decide

/-- Empty input length: branch to fail status. `H+68 → H+328`. -/
theorem tshEmptyLenBeq_taken (lenW : Word) (hlen : lenW = 0) :
    cpsTripleWithin 1 (H + 68) tshFailLiPC fullCode
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x9 .x0 tshEmptyLenBeqOff lenW 0 (H + 68)
  rw [tshEmptyLenBeq_taken_pc] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 68) 17
        (.BEQ .x9 .x0 tshEmptyLenBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbeq)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hlen)

/-- Non-empty length: fall through to header parse. `H+68 → H+72`. -/
theorem tshEmptyLenBeq_ntaken (lenW : Word) (hlen : lenW ≠ 0) :
    cpsTripleWithin 1 (H + 68) (H + 72) fullCode
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x9 .x0 tshEmptyLenBeqOff lenW 0 (H + 68)
  rw [show (H + 68 : Word) + 4 = H + 72 from by decide] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 68) 17
        (.BEQ .x9 .x0 tshEmptyLenBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbeq)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hlen ((sepConj_pure_right _).1 hBP).2)

/-! ## Body: fail / success status reconverge (`H+320` / `H+328`)

    Success writes `a0 := 0` then jumps over the fail `li`; empty-length and
    other fail arms land on `li a0, 1`. Both meet the frame epilogue at
    `tshBodyExit = H+332`. -/

/-- Fail status: `li a0, 1` at `H+328 → H+332`. -/
theorem tshFailLi_spec (v10 : Word) :
    cpsTripleWithin 1 tshFailLiPC tshBodyExit fullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x10 v10 (1 : Word) tshFailLiPC (by decide)
  rw [show tshFailLiPC + 4 = tshBodyExit from by
    unfold tshFailLiPC; rw [tshBodyExit_eq]; decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl tshFailLiPC 82
      (.LI .x10 (1 : Word))
      (by rw [tsh_prog_length]; decide)
      (by unfold tshFailLiPC; decide) rfl) h0

/-- Empty-length failure path: beq-taken then `li a0,1`. `H+68 → H+332`. -/
theorem tshEmptyLenFail_spec (lenW v10 : Word) (hlen : lenW = 0) :
    cpsTripleWithin 2 (H + 68) tshBodyExit fullCode
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (1 : Word))) := by
  have hbr := tshEmptyLenBeq_taken lenW hlen
  have hbrF := cpsTripleWithin_frameR (.x10 ↦ᵣ v10) (by pcf) hbr
  have hli := tshFailLi_spec v10
  have hliF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ lenW) ** (.x0 ↦ᵣ (0 : Word))) (by pcf) hli
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hbrF hliF
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

/-- Success status: `li a0, 0` at `H+320 → H+324`. -/
theorem tshSuccessLi_spec (v10 : Word) :
    cpsTripleWithin 1 (H + 320) (H + 324) fullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x10 v10 (0 : Word) (H + 320) (by decide)
  rw [show (H + 320 : Word) + 4 = H + 324 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 320) 80
      (.LI .x10 (0 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- Unconditional skip of fail `li`: `jal x0, +8` at `H+324 → H+332`, framed. -/
theorem tshSuccessSkipFail_spec (P : Assertion) (hP : P.pcFree) :
    cpsTripleWithin 1 (H + 324) tshBodyExit fullCode P P := by
  have h0 := jal_x0_spec_gen_within (8 : BitVec 21) (H + 324)
  rw [show (H + 324 : Word) + signExtend21 (8 : BitVec 21) = tshBodyExit from by
    rw [tshBodyExit_eq]; decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 324) 81
      (.JAL .x0 (8 : BitVec 21))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have hF := cpsTripleWithin_frameL P hP l0
  exact (sepConj_emp_right' P) ▸ hF

/-- Success reconverge: `li a0,0; jal skip`. `H+320 → H+332`. -/
theorem tshSuccessStatus_spec (v10 : Word) :
    cpsTripleWithin 2 (H + 320) tshBodyExit fullCode
      (.x10 ↦ᵣ v10) (.x10 ↦ᵣ (0 : Word)) := by
  have hli := tshSuccessLi_spec v10
  have hjal := tshSuccessSkipFail_spec (.x10 ↦ᵣ (0 : Word)) (by pcf)
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hli hjal)

/-! ## Body: list-header parse (`H+72`), short-list arm

    `lbu` first input byte; reject `< 0xc0`; short list (`< 0xf8`) sets
    `s5 := 1` (header length) via the taken `bltu` to `H+104`. Long-list
    arm (`≥ 0xf8`) is left for a later slice. -/

abbrev tshHdrByte (input : List (BitVec 8)) (h0 : 0 < input.length) : Word :=
  (input[0]'h0).zeroExtend 64

/-- `lbu t0, 0(s0)` — load RLP list header byte. `H+72 → H+76`. -/
theorem tshHdrLbu_spec (inPtr v5 : Word) (input : List (BitVec 8))
    (h0 : 0 < input.length)
    (halign : inPtr.toNat % 8 = 0)
    (hover : inPtr.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess inPtr = true) :
    cpsTripleWithin 1 (H + 72) (H + 76) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ tshHdrByte input h0) **
        bytesRegion inPtr input) := by
  have hptr : inPtr + BitVec.ofNat 64 0 = inPtr := by bv_omega
  have hlbu := bytesRegion_lbu_within .x5 .x8 inPtr v5 (H + 72) input 0
    (by decide) halign h0 (by omega) (by rwa [hptr])
  rw [hptr, show (H + 72 : Word) + 4 = H + 76 from by decide] at hlbu
  change cpsTripleWithin 1 (H + 72) (H + 76)
      (CodeReq.singleton (H + 72) (.LBU .x5 .x8 0))
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ tshHdrByte input h0) **
        bytesRegion inPtr input) at hlbu
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 72) 18
      (.LBU .x5 .x8 (0 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) hlbu

/-- `li t1, 192`. `H+76 → H+80`. -/
theorem tshHdrLi192_spec (v6 : Word) :
    cpsTripleWithin 1 (H + 76) (H + 80) fullCode
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (192 : Word)) := by
  have h0 := li_spec_gen_within .x6 v6 (192 : Word) (H + 76) (by decide)
  rw [show (H + 76 : Word) + 4 = H + 80 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 76) 19
      (.LI .x6 (192 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

abbrev tshNotListBeqOff : BitVec 13 := (248 : BitVec 13)

theorem tshNotListBeq_taken_pc :
    (H + 80) + signExtend13 tshNotListBeqOff = tshFailLiPC := by
  unfold tshNotListBeqOff tshFailLiPC H; decide

/-- Header `< 0xc0`: fail. `H+80 → H+328`. -/
theorem tshHdrNotList_taken (hdr : Word) (hult : BitVec.ult hdr (192 : Word)) :
    cpsTripleWithin 1 (H + 80) tshFailLiPC fullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 tshNotListBeqOff hdr (192 : Word) (H + 80)
  rw [tshNotListBeq_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 80) 20
        (.BLTU .x5 .x6 tshNotListBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hult)

/-- Header `≥ 0xc0`: continue. `H+80 → H+84`. -/
theorem tshHdrNotList_ntaken (hdr : Word) (hge : ¬BitVec.ult hdr (192 : Word)) :
    cpsTripleWithin 1 (H + 80) (H + 84) fullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (192 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 tshNotListBeqOff hdr (192 : Word) (H + 80)
  rw [show (H + 80 : Word) + 4 = H + 84 from by decide] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 80) 20
        (.BLTU .x5 .x6 tshNotListBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hge ((sepConj_pure_right _).1 hBP).2)

/-- `li t1, 248`. `H+84 → H+88`. -/
theorem tshHdrLi248_spec (v6 : Word) :
    cpsTripleWithin 1 (H + 84) (H + 88) fullCode
      (.x6 ↦ᵣ v6) (.x6 ↦ᵣ (248 : Word)) := by
  have h0 := li_spec_gen_within .x6 v6 (248 : Word) (H + 84) (by decide)
  rw [show (H + 84 : Word) + 4 = H + 88 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 84) 21
      (.LI .x6 (248 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

abbrev tshShortListBeqOff : BitVec 13 := (16 : BitVec 13)
abbrev tshShortHdrLiPC : Word := H + 104

theorem tshShortListBeq_taken_pc :
    (H + 88) + signExtend13 tshShortListBeqOff = tshShortHdrLiPC := by
  unfold tshShortListBeqOff tshShortHdrLiPC H; decide

/-- Short list (`hdr < 0xf8`): jump to `li s5, 1`. `H+88 → H+104`. -/
theorem tshHdrShortList_taken (hdr : Word) (hult : BitVec.ult hdr (248 : Word)) :
    cpsTripleWithin 1 (H + 88) tshShortHdrLiPC fullCode
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word)))
      ((.x5 ↦ᵣ hdr) ** (.x6 ↦ᵣ (248 : Word))) := by
  have hbr := bltu_spec_gen_within .x5 .x6 tshShortListBeqOff hdr (248 : Word) (H + 88)
  rw [tshShortListBeq_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 88) 22
        (.BLTU .x5 .x6 tshShortListBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hult)

/-- `li s5, 1` — short-list header length. `H+104 → H+108`. -/
theorem tshShortHdrLi_spec (v21 : Word) :
    cpsTripleWithin 1 tshShortHdrLiPC (H + 108) fullCode
      (.x21 ↦ᵣ v21) (.x21 ↦ᵣ (1 : Word)) := by
  have h0 := li_spec_gen_within .x21 v21 (1 : Word) tshShortHdrLiPC (by decide)
  rw [show tshShortHdrLiPC + 4 = H + 108 from by
    unfold tshShortHdrLiPC; decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl tshShortHdrLiPC 26
      (.LI .x21 (1 : Word))
      (by rw [tsh_prog_length]; decide)
      (by unfold tshShortHdrLiPC; decide) rfl) h0

/-- Short-list header parse through `s5 := 1`.
    Requires nonempty input, dword-aligned `inPtr`, and `0xc0 ≤ hdr < 0xf8`.
    `H+72 → H+108`. -/
theorem tshHdrParseShort_spec (inPtr v5 v6 v21 : Word) (input : List (BitVec 8))
    (h0 : 0 < input.length)
    (halign : inPtr.toNat % 8 = 0)
    (hover : inPtr.toNat < 2 ^ 64)
    (hvalid : isValidByteAccess inPtr = true)
    (hge : ¬BitVec.ult (tshHdrByte input h0) (192 : Word))
    (hult : BitVec.ult (tshHdrByte input h0) (248 : Word)) :
    cpsTripleWithin 7 (H + 72) (H + 108) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x21 ↦ᵣ v21) **
        bytesRegion inPtr input)
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ tshHdrByte input h0) ** (.x6 ↦ᵣ (248 : Word)) **
        (.x21 ↦ᵣ (1 : Word)) ** bytesRegion inPtr input) := by
  have hlbu := tshHdrLbu_spec inPtr v5 input h0 halign hover hvalid
  have hlbuF := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x21 ↦ᵣ v21)) (by pcf) hlbu
  have hli192 := tshHdrLi192_spec v6
  have hli192F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ tshHdrByte input h0) ** (.x21 ↦ᵣ v21) **
      bytesRegion inPtr input) (by pcf) hli192
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hlbuF hli192F
  have hnt := tshHdrNotList_ntaken (tshHdrByte input h0) hge
  have hntF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ v21) ** bytesRegion inPtr input) (by pcf) hnt
  have c012 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01 hntF
  have hli248 := tshHdrLi248_spec (192 : Word)
  have hli248F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ tshHdrByte input h0) ** (.x21 ↦ᵣ v21) **
      bytesRegion inPtr input) (by pcf) hli248
  have c0123 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c012 hli248F
  have htk := tshHdrShortList_taken (tshHdrByte input h0) hult
  have htkF := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x21 ↦ᵣ v21) ** bytesRegion inPtr input) (by pcf) htk
  have c01234 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c0123 htkF
  have hli1 := tshShortHdrLi_spec v21
  have hli1F := cpsTripleWithin_frameR
    ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ tshHdrByte input h0) ** (.x6 ↦ᵣ (248 : Word)) **
      bytesRegion inPtr input) (by pcf) hli1
  have c := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    c01234 hli1F
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) c)

/-! ## Body: nth-call setup after short header (`H+108 → H+156`)

    `li s6, 0`; if `nFields ≠ 0`, `index := nFields - 1`, shuffle ABI args,
    materialize `tsh_buf+64` / `+72` scratch pointers, then JAL nth. -/

/-- `li s6, 0`. `H+108 → H+112`. -/
theorem tshPayloadOffInit_spec (v22 : Word) :
    cpsTripleWithin 1 (H + 108) (H + 112) fullCode
      (.x22 ↦ᵣ v22) (.x22 ↦ᵣ (0 : Word)) := by
  have h0 := li_spec_gen_within .x22 v22 (0 : Word) (H + 108) (by decide)
  rw [show (H + 108 : Word) + 4 = H + 112 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 108) 27
      (.LI .x22 (0 : Word))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

abbrev tshNFieldsBeqOff : BitVec 13 := (76 : BitVec 13)
abbrev tshSkipNthPC : Word := H + 188

theorem tshNFieldsBeq_taken_pc :
    (H + 112) + signExtend13 tshNFieldsBeqOff = tshSkipNthPC := by
  unfold tshNFieldsBeqOff tshSkipNthPC H; decide

/-- `nFields = 0`: skip nth. `H+112 → H+188`. -/
theorem tshNFieldsBeq_taken (nFields : Word) (hz : nFields = 0) :
    cpsTripleWithin 1 (H + 112) tshSkipNthPC fullCode
      ((.x18 ↦ᵣ nFields) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x18 ↦ᵣ nFields) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x18 .x0 tshNFieldsBeqOff nFields 0 (H + 112)
  rw [tshNFieldsBeq_taken_pc] at hbeq
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 112) 28
        (.BEQ .x18 .x0 tshNFieldsBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbeq)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact ((sepConj_pure_right _).1 hBP).2 hz)

/-- `nFields ≠ 0`: fall through to nth setup. `H+112 → H+116`. -/
theorem tshNFieldsBeq_ntaken (nFields : Word) (hnz : nFields ≠ 0) :
    cpsTripleWithin 1 (H + 112) (H + 116) fullCode
      ((.x18 ↦ᵣ nFields) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x18 ↦ᵣ nFields) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x18 .x0 tshNFieldsBeqOff nFields 0 (H + 112)
  rw [show (H + 112 : Word) + 4 = H + 116 from by decide] at hbeq
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 112) 28
        (.BEQ .x18 .x0 tshNFieldsBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbeq)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact hnz ((sepConj_pure_right _).1 hBP).2)

/-- `addi t0, s2, -1` — last-field index. `H+116 → H+120`. -/
theorem tshNthIndex_spec (nFields v5 : Word) :
    cpsTripleWithin 1 (H + 116) (H + 120) fullCode
      ((.x18 ↦ᵣ nFields) ** (.x5 ↦ᵣ v5))
      ((.x18 ↦ᵣ nFields) ** (.x5 ↦ᵣ (nFields + signExtend12 (-1 : BitVec 12)))) := by
  have h0 := addi_spec_gen_within .x5 .x18 v5 nFields (-1 : BitVec 12) (H + 116)
    (by decide)
  rw [show (H + 116 : Word) + 4 = H + 120 from by decide] at h0
  exact cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 116) 29
      (.ADDI .x5 .x18 (-1 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0

/-- Three ABI MVs for nth: `a0:=s0, a1:=s1, a2:=t0`. `H+120 → H+132`. -/
theorem tshNthArgMoves_spec
    (inPtr lenW indexW v10 v11 v12 : Word) :
    cpsTripleWithin 3 (H + 120) (H + 132) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ indexW)) := by
  have h0 := mv_spec_gen_within .x10 .x8 inPtr v10 (H + 120) (by decide)
  rw [show (H + 120 : Word) + 4 = H + 124 from by decide] at h0
  have l0 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 120) 30 (.MV .x10 .x8)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h0
  have c0 : cpsTripleWithin 1 (H + 120) (H + 124) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12)) := by
    have hF := cpsTripleWithin_frameR
      ((.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      (by pcf) l0
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have h1 := mv_spec_gen_within .x11 .x9 lenW v11 (H + 124) (by decide)
  rw [show (H + 124 : Word) + 4 = H + 128 from by decide] at h1
  have l1 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 124) 31 (.MV .x11 .x9)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h1
  have c1 : cpsTripleWithin 1 (H + 124) (H + 128) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ v12)) := by
    have hF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) ** (.x5 ↦ᵣ indexW) ** (.x10 ↦ᵣ inPtr) ** (.x12 ↦ᵣ v12))
      (by pcf) l1
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  have c01 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c0 c1
  have h2 := mv_spec_gen_within .x12 .x5 indexW v12 (H + 128) (by decide)
  rw [show (H + 128 : Word) + 4 = H + 132 from by decide] at h2
  have l2 := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 128) 32 (.MV .x12 .x5)
      (by rw [tsh_prog_length]; decide) (by decide) rfl) h2
  have c2 : cpsTripleWithin 1 (H + 128) (H + 132) fullCode
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ v12))
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x5 ↦ᵣ indexW) **
        (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ indexW)) := by
    have hF := cpsTripleWithin_frameR
      ((.x8 ↦ᵣ inPtr) ** (.x9 ↦ᵣ lenW) ** (.x10 ↦ᵣ inPtr) ** (.x11 ↦ᵣ lenW))
      (by pcf) l2
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) hF
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c01 c2

/-! ## Body: materialize nth scratch pointers (`H+132 → H+156`) -/

theorem tsh_la_nth_off_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132) =
      Rv64.laHi (H + 132) TshBuf := by
  decide

theorem tsh_la_nth_off_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 132) =
      Rv64.laLo (H + 132) TshBuf := by
  decide

theorem tsh_la_nth_off_range : laInRange (H + 132) TshBuf := by
  decide

theorem tsh_la_nth_len_hi :
    Codegen.laHi GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144) =
      Rv64.laHi (H + 144) TshBuf := by
  decide

theorem tsh_la_nth_len_lo :
    Codegen.laLo GuestAddrs.tsh_buf (GuestAddrs.tx_signing_hash + 144) =
      Rv64.laLo (H + 144) TshBuf := by
  decide

theorem tsh_la_nth_len_range : laInRange (H + 144) TshBuf := by
  decide

/-- `la a3, tsh_buf; addi a3, a3, 64` → `tshNthOffPtr`. `H+132 → H+144`. -/
theorem tshNthOffPtr_spec (v13 : Word) :
    cpsTripleWithin 3 (H + 132) (H + 144) fullCode
      (.x13 ↦ᵣ v13) (.x13 ↦ᵣ tshNthOffPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 132)
        (.AUIPC .x13 (Rv64.laHi (H + 132) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 132) 33
      (.AUIPC .x13 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 132)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_nth_off_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 132) + 4)
        (.ADDI .x13 .x13 (Rv64.laLo (H + 132) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 136) 34
      (.ADDI .x13 .x13 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 132)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 132 : Word) + 4 = H + 136 := by decide
    rw [hpc, ← tsh_la_nth_off_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x13 v13 (H + 132) TshBuf
    (by decide) tsh_la_nth_off_range hau had
  rw [show (H + 132 : Word) + 8 = H + 140 from by decide] at hla
  have haddi := addi_spec_gen_same_within .x13 TshBuf (64 : BitVec 12) (H + 140)
    (by decide)
  rw [show (H + 140 : Word) + 4 = H + 144 from by decide,
      show TshBuf + signExtend12 (64 : BitVec 12) = tshNthOffPtr from by
        unfold tshNthOffPtr TshBuf; decide] at haddi
  have laddi := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 140) 35
      (.ADDI .x13 .x13 (64 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) haddi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr hla laddi)

/-- `la a4, tsh_buf; addi a4, a4, 72` → `tshNthLenPtr`. `H+144 → H+156`. -/
theorem tshNthLenPtr_spec (v14 : Word) :
    cpsTripleWithin 3 (H + 144) (H + 156) fullCode
      (.x14 ↦ᵣ v14) (.x14 ↦ᵣ tshNthLenPtr) := by
  have hau : ∀ a i,
      CodeReq.singleton (H + 144)
        (.AUIPC .x14 (Rv64.laHi (H + 144) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 144) 36
      (.AUIPC .x14 (Codegen.laHi GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 144)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    exact hmem a i (by rwa [← tsh_la_nth_len_hi] at hi)
  have had : ∀ a i,
      CodeReq.singleton ((H + 144) + 4)
        (.ADDI .x14 .x14 (Rv64.laLo (H + 144) TshBuf)) a = some i →
        fullCode a = some i := by
    intro a i hi
    have hmem := tshMem (txSigningHash_prog : List Instr) rfl (H + 148) 37
      (.ADDI .x14 .x14 (Codegen.laLo GuestAddrs.tsh_buf
        (GuestAddrs.tx_signing_hash + 144)))
      (by rw [tsh_prog_length]; decide) (by decide) rfl
    have hpc : (H + 144 : Word) + 4 = H + 148 := by decide
    rw [hpc, ← tsh_la_nth_len_lo] at hi
    exact hmem a i hi
  have hla := la_materialize_within .x14 v14 (H + 144) TshBuf
    (by decide) tsh_la_nth_len_range hau had
  rw [show (H + 144 : Word) + 8 = H + 152 from by decide] at hla
  have haddi := addi_spec_gen_same_within .x14 TshBuf (72 : BitVec 12) (H + 152)
    (by decide)
  rw [show (H + 152 : Word) + 4 = H + 156 from by decide,
      show TshBuf + signExtend12 (72 : BitVec 12) = tshNthLenPtr from by
        unfold tshNthLenPtr TshBuf; decide] at haddi
  have laddi := cpsTripleWithin_extend_code
    (tshMem (txSigningHash_prog : List Instr) rfl (H + 152) 38
      (.ADDI .x14 .x14 (72 : BitVec 12))
      (by rw [tsh_prog_length]; decide) (by decide) rfl) haddi
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_seq_same_cr hla laddi)

/-- Combined pointer materialization. `H+132 → H+156`. -/
theorem tshNthPtrs_spec (v13 v14 : Word) :
    cpsTripleWithin (3 + 3) (H + 132) (H + 156) fullCode
      ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))
      ((.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr)) := by
  have h1 := tshNthOffPtr_spec v13
  have h1F := cpsTripleWithin_frameR (.x14 ↦ᵣ v14) (by pcf) h1
  have h1W : cpsTripleWithin 3 (H + 132) (H + 144) fullCode
      ((.x13 ↦ᵣ v13) ** (.x14 ↦ᵣ v14))
      ((.x14 ↦ᵣ v14) ** (.x13 ↦ᵣ tshNthOffPtr)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h1F
  have h2 := tshNthLenPtr_spec v14
  have h2F := cpsTripleWithin_frameR (.x13 ↦ᵣ tshNthOffPtr) (by pcf) h2
  have h2W : cpsTripleWithin 3 (H + 144) (H + 156) fullCode
      ((.x14 ↦ᵣ v14) ** (.x13 ↦ᵣ tshNthOffPtr))
      ((.x13 ↦ᵣ tshNthOffPtr) ** (.x14 ↦ᵣ tshNthLenPtr)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h2F
  exact cpsTripleWithin_seq_same_cr h1W h2W

/-! ## Body: post-nth status check (`H+160`)

    `bne a0, x0` — nonzero nth status jumps to fail `li`; success falls
    through to payload-length compute + prefix setup. -/

abbrev tshNthFailBeqOff : BitVec 13 := (168 : BitVec 13)

theorem tshNthFailBeq_taken_pc :
    (H + 160) + signExtend13 tshNthFailBeqOff = tshFailLiPC := by
  unfold tshNthFailBeqOff tshFailLiPC H; decide

/-- nth returned nonzero: fail. `H+160 → H+328`. -/
theorem tshNthFail_taken (st : Word) (hnz : st ≠ 0) :
    cpsTripleWithin 1 (H + 160) tshFailLiPC fullCode
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 tshNthFailBeqOff st 0 (H + 160)
  rw [tshNthFailBeq_taken_pc] at hbr
  exact cpsBranchWithin_takenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 160) 40
        (.BNE .x10 .x0 tshNthFailBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbr)
    (fun _hp hQf => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQf
      exact hnz ((sepConj_pure_right _).1 hBP).2)

/-- nth returned 0: continue. `H+160 → H+164`. -/
theorem tshNthFail_ntaken (st : Word) (hz : st = 0) :
    cpsTripleWithin 1 (H + 160) (H + 164) fullCode
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x10 ↦ᵣ st) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbr := bne_spec_gen_within .x10 .x0 tshNthFailBeqOff st 0 (H + 160)
  rw [show (H + 160 : Word) + 4 = H + 164 from by decide] at hbr
  exact cpsBranchWithin_ntakenStripPure2
    (cpsBranchWithin_extend_code
      (tshMem (txSigningHash_prog : List Instr) rfl (H + 160) 40
        (.BNE .x10 .x0 tshNthFailBeqOff)
        (by rw [tsh_prog_length]; decide) (by decide) rfl) hbr)
    (fun _hp hQt => by
      obtain ⟨_, _, _, _, _, hBP⟩ := hQt
      exact ((sepConj_pure_right _).1 hBP).2 hz)


end EvmAsm.Codegen.TxSigningHashSpec
