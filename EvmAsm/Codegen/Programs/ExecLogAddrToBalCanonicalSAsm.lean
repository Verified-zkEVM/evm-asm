/-
  EvmAsm.Codegen.Programs.ExecLogAddrToBalCanonicalSAsm

  Proof-first (DCode) port of `exec_log_addr_to_bal_canonical`: reverse
  the low 20 bytes of the 32-byte exec-log address key at `a0` into the
  writable 20-byte canonical-BE output at `a1` (docs/sasm-deriv.md).

  The derivation is a calc chain — init block, a `dwhileHeader` loop
  (the original reloads the limit register by `li t1, 20` before every
  guard evaluation, which is exactly the `whileHeader` shape), and a
  pure exit step — and the code is GENERATED from it; the byte pins
  below and the assemble+cmp check tie it byte-identically to the
  hand-written routine in `Programs/StorageReadLog.lean`.

  The window algebra (`revByte`/`revWin`) and the read-only-load helper
  are reused from the proven generic reverse core in
  `SwrRevLeBeSAsm.lean` (len := 20).
-/

import EvmAsm.Rv64.SAsm.Deriv
import EvmAsm.Codegen.Programs.SwrRevLeBeSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open SwrRevLeBeSAsm (revByte revWin revWin_zero length_revWin revWin_step
  revWin_len_eq execInstrRF_lbu_ro)

namespace ExecLogAddrToBalCanonicalSAsm

/-! ## The routine's pieces -/

/-- Loop body: recompute the descending source index from the counter,
    load `src[19-i]`, store it at `dst[i]`, bump the counter. -/
def elatbcStepBlock : List Instr :=
  [ .LI .x7 (19 : Word),
    .SUB .x7 .x7 .x5,
    .ADD .x7 .x10 .x7,
    .LBU .x28 .x7 0,
    .ADD .x29 .x11 .x5,
    .SB .x29 .x28 0,
    .ADDI .x5 .x5 (1 : BitVec 12) ]

/-- Reloaded header: `li t1, 20` before every guard evaluation. -/
def elatbcHeaderBlock : List Instr := [ .LI .x6 (20 : Word) ]

/-- Register file after one loop body (given the loaded byte `b`). -/
def elatbcStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x7 (19 : Word)
  let r2 := r1.set .x7 (r1.get .x7 - r1.get .x5)
  let r3 := r2.set .x7 (r2.get .x10 + r2.get .x7)
  let r4 := r3.set .x28 (b.zeroExtend 64)
  let r5 := r4.set .x29 (r4.get .x11 + r4.get .x5)
  r5.set .x5 (r5.get .x5 + signExtend12 (1 : BitVec 12))

theorem elatbcStepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (elatbcStepRf rf b).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold elatbcStepRf
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7)]

theorem elatbcStepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (elatbcStepRf rf b).get .x10 = rf.get .x10 := by
  unfold elatbcStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7)]

theorem elatbcStepRf_get_x11 (rf : RegFile) (b : BitVec 8) :
    (elatbcStepRf rf b).get .x11 = rf.get .x11 := by
  unfold elatbcStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7)]

/-! ## The step engine -/

section Engine

variable (src dst : Word) (bs : List (BitVec 8))

/-- The recomputed source cursor after the three ALU instructions. -/
theorem elatbc_cursor (rf : RegFile) (i : Nat)
    (hx5 : rf.get .x5 = BitVec.ofNat 64 i)
    (hx10 : rf.get .x10 = src) (hi : i < 20) :
    (((rf.set .x7 (19 : Word)).set .x7
        ((rf.set .x7 (19 : Word)).get .x7
          - (rf.set .x7 (19 : Word)).get .x5)).set .x7
      ((((rf.set .x7 (19 : Word)).set .x7
        ((rf.set .x7 (19 : Word)).get .x7
          - (rf.set .x7 (19 : Word)).get .x5))).get .x10
        + (((rf.set .x7 (19 : Word)).set .x7
        ((rf.set .x7 (19 : Word)).get .x7
          - (rf.set .x7 (19 : Word)).get .x5))).get .x7)).get .x7
      = src + BitVec.ofNat 64 (19 - i) := by
    rw [RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
      RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
      hx5, hx10]
    have h1 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]; omega
    have h2 : (BitVec.ofNat 64 (19 - i)).toNat = 19 - i := by
      rw [BitVec.toNat_ofNat]; omega
    bv_omega

/-- Engine: one loop body loads `src[19-i]`, stores it at `dst[i]`, and
    bumps the counter. -/
theorem elatbc_step_engine (i : Nat) (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = BitVec.ofNat 64 i)
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst)
    (hi : i < 20)
    (hsrc : src.toNat + 20 < 2 ^ 64) (hdst : dst.toNat + 20 < 2 ^ 64)
    (hdisj : src.toNat + 20 ≤ dst.toNat ∨ dst.toNat + 20 ≤ src.toNat)
    (hws : ws.length = 20) :
    execBlock ⟨src, bs⟩ dst rf ws elatbcStepBlock
      = (elatbcStepRf rf (revByte bs 20 i),
         setBytes ws i [revByte bs 20 i]) := by
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h2 : (BitVec.ofNat 64 (19 - i)).toNat = 19 - i := by
    rw [BitVec.toNat_ofNat]; omega
  have hcur := elatbc_cursor src rf i hx5 hx10 hi
  -- the load address, in closed form
  have hla : ∀ rf3 : RegFile, rf3.get .x7 = src + BitVec.ofNat 64 (19 - i) →
      rf3.get .x7 + signExtend12 (0 : BitVec 12)
        = src + BitVec.ofNat 64 (19 - i) := by
    intro rf3 h
    rw [h, hse_0]; simp
  -- the load misses the writable window
  have hnr : ∀ a : Word, a = src + BitVec.ofNat 64 (19 - i) →
      ¬ inRw dst ws a 1 := by
    rintro a rfl
    unfold inRw
    rw [hws]
    have hsubd : (src + BitVec.ofNat 64 (19 - i) - dst).toNat
        = (src.toNat + (19 - i) + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
      congr 1; omega
    rw [hsubd]
    rcases hdisj with hd | hd <;> omega
  -- the loaded byte is the reversed source byte
  have hsub : (src + BitVec.ofNat 64 (19 - i) - src).toNat = 19 - i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, h2]; omega
  -- the store index is i
  have hstore : ∀ rf5 : RegFile, rf5.get .x29 = dst + BitVec.ofNat 64 i →
      (rf5.get .x29 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    intro rf5 h
    rw [h, hse_0]
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]; omega
    bv_omega
  rw [show elatbcStepBlock =
      [.LI .x7 (19 : Word), .SUB .x7 .x7 .x5, .ADD .x7 .x10 .x7,
       .LBU .x28 .x7 0, .ADD .x29 .x11 .x5, .SB .x29 .x28 0,
       .ADDI .x5 .x5 (1 : BitVec 12)] from rfl]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons,
    execInstrRF_lbu_ro _ _ _ _ _ _ _ (by rw [hla _ hcur]; exact hnr _ rfl)]
  dsimp only
  rw [show Region.byteAt ⟨src, bs⟩ _ = revByte bs 20 i from by
    rw [hla _ hcur]
    show bs.getD ((src + BitVec.ofNat 64 (19 - i) - src).toNat) 0
      = revByte bs 20 i
    rw [hsub]; rfl]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i
    (by
      refine hstore _ ?_
      rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        hx11, hx5])]
  dsimp only
  have hb : ∀ (r : RegFile) (w : Word),
      (((r.set .x28 ((revByte bs 20 i).zeroExtend 64)).set .x29 w).get .x28)
        = (revByte bs 20 i).zeroExtend 64 := by
    intro r w
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
      RegFile.get_set_self _ _ _ (by decide)]
  rw [hb, truncate_zeroExtend_byte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold elatbcStepRf
  rw [setBytes_singleton]

end Engine

/-! ## The derivation -/

section Deriv

variable (src dst : Word) (bs orig : List (BitVec 8))

/-- Static facts, carried through the loop. -/
def elatbcStatic : Prop :=
  orig.length = 20 ∧ 20 ≤ bs.length ∧
  src.toNat + 20 < 2 ^ 64 ∧ dst.toNat + 20 < 2 ^ 64 ∧
  (src.toNat + 20 ≤ dst.toNat ∨ dst.toNat + 20 ≤ src.toNat)

/-- Loop invariant (at guard evaluation, after the header reload). -/
def elatbcInv (i : Nat) : Reach :=
  fun rf ws A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧ rf.get .x6 = (20 : Word) ∧
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ i ≤ 20 ∧
    elatbcStatic src dst bs orig ∧
    ws = revWin bs 20 orig i ∧ A = empAssertion

/-- Mid-states: after the i-th body, before the header reload. -/
def elatbcMid (i : Nat) : Reach :=
  fun rf ws A =>
    rf.get .x5 = BitVec.ofNat 64 (i + 1) ∧
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ i < 20 ∧
    elatbcStatic src dst bs orig ∧
    ws = revWin bs 20 orig (i + 1) ∧ A = empAssertion

local infix:36 " ⤳ " => DCode (Region.mk src bs) (RwRegion.mk dst 20)

/-- Reload the guard limit: entry run (`P1 ⤳ inv 0`) and per-iteration
    rerun share the same single-instruction skeleton. -/
private def headerPost (rf : RegFile) : Prop := rf.get .x6 = (20 : Word)

/-- Proof-first reverse copy: the calc chain from the ABI precondition to
    "the output window is the reversed low-20 source bytes". -/
def elatbcDeriv :
    (fun rf ws A => rf.get .x10 = src ∧ rf.get .x11 = dst ∧
      ws = orig ∧ elatbcStatic src dst bs orig ∧ A = empAssertion)
      ⤳ (fun _ ws A => ws = (bs.take 20).reverse ∧ A = empAssertion) :=
  calc (fun rf ws A => rf.get .x10 = src ∧ rf.get .x11 = dst ∧
        ws = orig ∧ elatbcStatic src dst bs orig ∧ A = empAssertion : Reach)
    _ ⤳ (fun rf ws A => rf.get .x5 = (0 : Word) ∧ rf.get .x10 = src ∧
          rf.get .x11 = dst ∧ ws = orig ∧
          elatbcStatic src dst bs orig ∧ A = empAssertion : Reach) :=
      DCode.block "init" [.LI .x5 (0 : Word)] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨h10, h11, hws, hst, hA⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          refine ⟨?_, ?_, ?_, hws, hst, hA⟩
          · rw [RegFile.get_set_self _ _ _ (by decide)]
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h10]
          · rw [RegFile.get_set_ne _ _ _ _ (by decide), h11])
    _ ⤳ (fun rf ws A => (∃ i, i ≤ 20 ∧ elatbcInv src dst bs orig i rf ws A)
          ∧ ¬ (Cond.bne .x5 .x6).holds rf : Reach) :=
      DCode.dwhileHeader "loop" (.bne .x5 .x6) 20
        (elatbcInv src dst bs orig) (elatbcMid src dst bs orig)
        (DCode.block "limit" elatbcHeaderBlock (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨h5, h10, h11, hws, hst, hA⟩
            simp only [elatbcHeaderBlock, execBlock_cons, execBlock_nil,
              execInstrRF, aluSem, elatbcInv]
            refine ⟨?_, ?_, ?_, ?_, by omega, hst, ?_, hA⟩
            · rw [RegFile.get_set_ne _ _ _ _ (by decide), h5]; rfl
            · rw [RegFile.get_set_self _ _ _ (by decide)]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide), h10]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide), h11]
            · rw [hws, revWin_zero]))
        (fun i =>
          DCode.block "limit" elatbcHeaderBlock (by decide)
            (fun h => absurd h (by decide))
            (by
              rintro rf ws A _ ⟨hi, h5, h10, h11, -, hst, hws, hA⟩
              simp only [elatbcHeaderBlock, execBlock_cons, execBlock_nil,
                execInstrRF, aluSem, elatbcInv]
              refine ⟨?_, ?_, ?_, ?_, by omega, hst, hws, hA⟩
              · rw [RegFile.get_set_ne _ _ _ _ (by decide), h5]
              · rw [RegFile.get_set_self _ _ _ (by decide)]
              · rw [RegFile.get_set_ne _ _ _ _ (by decide), h10]
              · rw [RegFile.get_set_ne _ _ _ _ (by decide), h11]))
        (fun i =>
          DCode.block "step" elatbcStepBlock (by decide)
            (by
              intro _ rf ws A hwslen hpre
              obtain ⟨hi, ⟨h5, h6, h10, h11, hile,
                ⟨hol, hlb, hsb, hdb, hdj⟩, hwin, hA⟩, hc⟩ := hpre
              have hws20 : ws.length = 20 := hwslen
              have h2 : (BitVec.ofNat 64 (19 - i)).toNat = 19 - i := by
                rw [BitVec.toNat_ofNat]; omega
              have hcur := elatbc_cursor src rf i h5 h10 hi
              have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by
                decide
              have hnr : ¬ inRw dst ws
                  (src + BitVec.ofNat 64 (19 - i)) 1 := by
                unfold inRw
                rw [hws20]
                have hsubd : (src + BitVec.ofNat 64 (19 - i) - dst).toNat
                    = (src.toNat + (19 - i) + (2 ^ 64 - dst.toNat))
                      % 2 ^ 64 := by
                  rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
                  congr 1; omega
                rw [hsubd]
                rcases hdj with hd | hd <;> omega
              have hsub : (src + BitVec.ofNat 64 (19 - i) - src).toNat
                  = 19 - i := by
                rw [BitVec.toNat_sub, BitVec.toNat_add, h2]; omega
              show blockVCs ⟨src, bs⟩ dst rf ws elatbcStepBlock
              rw [show elatbcStepBlock =
                  [.LI .x7 (19 : Word), .SUB .x7 .x7 .x5, .ADD .x7 .x10 .x7,
                   .LBU .x28 .x7 0, .ADD .x29 .x11 .x5, .SB .x29 .x28 0,
                   .ADDI .x5 .x5 (1 : BitVec 12)] from rfl]
              refine ⟨trivial, ?_⟩
              rw [show execInstrRF ⟨src, bs⟩ dst rf ws (.LI .x7 (19 : Word))
                  = (rf.set .x7 (19 : Word), ws) from rfl]
              refine ⟨trivial, ?_⟩
              rw [show execInstrRF ⟨src, bs⟩ dst (rf.set .x7 (19 : Word)) ws
                    (.SUB .x7 .x7 .x5)
                  = ((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5), ws) from rfl]
              refine ⟨trivial, ?_⟩
              rw [show execInstrRF ⟨src, bs⟩ dst
                    ((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5)) ws
                    (.ADD .x7 .x10 .x7)
                  = (((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5)).set .x7
                      ((((rf.set .x7 (19 : Word)).set .x7
                        ((rf.set .x7 (19 : Word)).get .x7
                          - (rf.set .x7 (19 : Word)).get .x5))).get .x10
                        + (((rf.set .x7 (19 : Word)).set .x7
                        ((rf.set .x7 (19 : Word)).get .x7
                          - (rf.set .x7 (19 : Word)).get .x5))).get .x7),
                     ws) from rfl]
              refine ⟨?_, ?_⟩
              · -- LBU obligation: routes to the read-only region, in range
                simp only [loadSem]
                rw [if_neg (by
                  rw [show _ + signExtend12 (0 : BitVec 12)
                      = src + BitVec.ofNat 64 (19 - i) from by
                    rw [hcur, hse_0]; simp]
                  exact hnr)]
                rw [show _ + signExtend12 (0 : BitVec 12)
                    = src + BitVec.ofNat 64 (19 - i) from by
                  rw [hcur, hse_0]; simp]
                show 1 ∣ (src + BitVec.ofNat 64 (19 - i) - src).toNat
                  ∧ (src + BitVec.ofNat 64 (19 - i) - src).toNat + 1
                    ≤ bs.length
                rw [hsub]
                exact ⟨Nat.one_dvd _, by omega⟩
              · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _
                  (by rw [show _ + signExtend12 (0 : BitVec 12)
                      = src + BitVec.ofNat 64 (19 - i) from by
                    rw [hcur, hse_0]; simp]; exact hnr)]
                refine ⟨trivial, ?_⟩
                dsimp only [execInstrRF, aluSem]
                -- SB obligation ∧ (ADDI ∧ nil)
                have hx29 : ∀ (r : RegFile) (v : Word),
                    ((r.set .x29 v).get .x29
                      + signExtend12 (0 : BitVec 12) - dst).toNat
                      = (v + signExtend12 (0 : BitVec 12) - dst).toNat := by
                  intro r v
                  rw [RegFile.get_set_self _ _ _ (by decide)]
                have hval : (((((rf.set .x7 (19 : Word)).set .x7
                    ((rf.set .x7 (19 : Word)).get .x7
                      - (rf.set .x7 (19 : Word)).get .x5)).set .x7
                    ((((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5))).get .x10
                      + (((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5))).get .x7)).set
                    .x28 ((revByte bs 20 i).zeroExtend 64)).get .x11
                    + ((((rf.set .x7 (19 : Word)).set .x7
                    ((rf.set .x7 (19 : Word)).get .x7
                      - (rf.set .x7 (19 : Word)).get .x5)).set .x7
                    ((((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5))).get .x10
                      + (((rf.set .x7 (19 : Word)).set .x7
                      ((rf.set .x7 (19 : Word)).get .x7
                        - (rf.set .x7 (19 : Word)).get .x5))).get .x7)).set
                    .x28 ((revByte bs 20 i).zeroExtend 64)).get .x5)
                    = dst + BitVec.ofNat 64 i := by
                  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x28),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
                    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
                    h11, h5]
                have hidx : ∀ (r : RegFile) (v : Word),
                    r.get .x29 = dst + BitVec.ofNat 64 i →
                    (r.get .x29 + signExtend12 (0 : BitVec 12)
                      - dst).toNat = i := by
                  intro r v h
                  rw [h, hse_0]
                  have hi2 : (BitVec.ofNat 64 i).toNat = i := by
                    rw [BitVec.toNat_ofNat]; omega
                  bv_omega
                refine ⟨⟨?_, ?_⟩, trivial, trivial⟩
                · dsimp only
                  unfold inRw
                  rw [hidx _ 0 (by
                    rw [RegFile.get_set_self _ _ _ (by decide)]
                    exact hval), hws20]
                  omega
                · dsimp only
                  rw [hidx _ 0 (by
                    rw [RegFile.get_set_self _ _ _ (by decide)]
                    exact hval)]
                  exact Nat.one_dvd _)
            (by
              rintro rf ws A hwslen ⟨hi, ⟨h5, h6, h10, h11, hile,
                hst, hwin, hA⟩, hc⟩
              obtain ⟨hol, hlb, hsb, hdb, hdj⟩ := hst
              have hws20 : ws.length = 20 := hwslen
              rw [elatbc_step_engine src dst bs i rf ws h5 h10 h11 hi
                hsb hdb hdj hws20]
              refine ⟨?_, ?_, ?_, hi, ⟨hol, hlb, hsb, hdb, hdj⟩, ?_, hA⟩
              · rw [elatbcStepRf_get_x5, h5,
                  show signExtend12 (1 : BitVec 12) = (1 : Word) from
                    by decide]
                have h1 : (BitVec.ofNat 64 i).toNat = i := by
                  rw [BitVec.toNat_ofNat]; omega
                have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
                  rw [BitVec.toNat_ofNat]; omega
                bv_omega
              · rw [elatbcStepRf_get_x10, h10]
              · rw [elatbcStepRf_get_x11, h11]
              · rw [hwin, revWin_step bs 20 orig i hol hi]))
        (fun rf ws A h => by
          obtain ⟨h5, h6, -⟩ := h
          simp only [Cond.holds, ne_eq, not_not]
          rw [h5, h6]
          decide)
    _ ⤳ (fun _ ws A => ws = (bs.take 20).reverse ∧ A = empAssertion
          : Reach) :=
      DCode.pure "done"
        (by
          rintro rf ws A ⟨⟨i, hile, h5, h6, -, -, -,
            ⟨hol, hlb, -, -, -⟩, hwin, hA⟩, hc⟩
          simp only [Cond.holds, ne_eq, not_not] at hc
          have hi20 : i = 20 := by
            rw [h5, h6] at hc
            have h20 : ((20 : Word)).toNat = 20 := rfl
            have := congrArg BitVec.toNat hc
            rw [BitVec.toNat_ofNat, h20] at this
            omega
          subst hi20
          exact ⟨by rw [hwin, revWin_len_eq bs 20 orig hol hlb], hA⟩)

/-! ## The generated function, spec, and code -/

/-- The generated SAsm function. -/
def elatbcFn : Fn :=
  (elatbcDeriv src dst bs orig).fn "exec_log_addr_to_bal_canonical"

/-- Machine-level correctness of the generated body at any base: from the
    ABI precondition, the 20-byte output window ends as the reversed
    low-20 source bytes. -/
theorem elatbcFn_spec
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, 20⟩)
    (base : Word) : (elatbcFn src dst bs orig).Spec base :=
  DCode.fn_spec "exec_log_addr_to_bal_canonical"
    (elatbcDeriv src dst bs orig) base hwf hrww

end Deriv

/-- The generated code with the return epilogue — the routine the guest
    emits (drift tie in `StorageReadLog.lean`). -/
def execLogAddrToBalCanonical_prog : Program :=
  (elatbcFn 0 0 [] []).programRet 0

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

-- Pinned instruction sequence (build-time evaluation): init, reloaded
-- header, guard, 7-instruction body, back-edge, ret — byte-identical to
-- the hand-written routine.
#guard (execLogAddrToBalCanonical_prog : List Instr) ==
    [ .LI .x5 (0 : Word),
      .LI .x6 (20 : Word),
      .BEQ .x5 .x6 (36 : BitVec 13),
      .LI .x7 (19 : Word),
      .SUB .x7 .x7 .x5,
      .ADD .x7 .x10 .x7,
      .LBU .x28 .x7 0,
      .ADD .x29 .x11 .x5,
      .SB .x29 .x28 0,
      .ADDI .x5 .x5 (1 : BitVec 12),
      .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 36)),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard execLogAddrToBalCanonical_prog.length = 12

-- The code does not depend on the ghost arguments (sampled).
#guard ((elatbcFn 5 7 [1] [2]).programRet 0 : List Instr)
    == (execLogAddrToBalCanonical_prog : List Instr)

end ExecLogAddrToBalCanonicalSAsm

end EvmAsm.Codegen
