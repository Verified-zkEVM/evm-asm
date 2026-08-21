/-
  EvmAsm.Codegen.Programs.SenderPostNonceConsistentSAsm

  Proof-first (DCode) port of `sender_post_nonce_consistent` — the BAL
  verdict slice checking `post_nonce == pre_nonce + 1` on the sender's
  lookup record (`a0` = record ptr; returns 0 consistent / 1 mismatch /
  2 skip when the post nonce is absent (`UINT64_MAX` length) or wider
  than a u64).

  Second guard-cascade consumer, composing three ret-shapes at once:
  `retCascade` (two skip guards into the shared `li a0,2; ret` tail),
  whose ok tail is init + a `dwhile` BE-accumulate loop + a pure exit +
  a compare block + a `dretIf` (0/1 tails).  Byte-identity `#guard`-
  pinned against the already-converted `senderPostNonceConsistent_prog`
  (no Codegen change; its emitted string carries an rfl drift theorem).
-/

import EvmAsm.Rv64.SAsm.Deriv
import EvmAsm.Codegen.Programs.SenderPostNonceConsistent
import EvmAsm.Codegen.Programs.SwrRevLeBeSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

open SwrRevLeBeSAsm (execInstrRF_lbu_ro)

namespace SenderPostNonceConsistentSAsm

/-! ## The routine's semantics -/

/-- Big-endian accumulate: `acc ← acc <<< 8 ||| b`. -/
def beAcc (bytes : List (BitVec 8)) : Word :=
  bytes.foldl (fun a b => (a <<< (8 : Nat)) ||| b.zeroExtend 64) 0

theorem beAcc_take_succ (bytes : List (BitVec 8)) (i : Nat)
    (h : i < bytes.length) :
    beAcc (bytes.take (i + 1))
      = (beAcc (bytes.take i) <<< (8 : Nat)) ||| bytes[i].zeroExtend 64 := by
  unfold beAcc
  rw [show bytes.take (i + 1) = bytes.take i ++ [bytes[i]] from by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    rfl]
  rw [List.foldl_append]
  rfl

/-- The record's declared post-nonce byte length (LE u64 at `+128`). -/
def spncLen (bs : List (BitVec 8)) : Word :=
  packBytes ((bs.drop 128).take 8)

/-- The record's pre nonce (LE u64 at `+80`). -/
def spncPre (bs : List (BitVec 8)) : Word :=
  packBytes ((bs.drop 80).take 8)

/-- The skip condition: post nonce absent or wider than a u64. -/
def spncSkip (bs : List (BitVec 8)) : Prop :=
  spncLen bs = (-1 : Word) ∨ BitVec.ult (8 : Word) (spncLen bs) = true

instance (bs : List (BitVec 8)) : Decidable (spncSkip bs) := by
  unfold spncSkip
  infer_instance

/-- The verdict. -/
def spncOut (bs : List (BitVec 8)) : Word :=
  if spncSkip bs then 2
  else if beAcc ((bs.drop 136).take (spncLen bs).toNat)
      = spncPre bs + 1 then 0 else 1

/-! ## Structure -/

def spncStages : List (List Instr × Cond) :=
  [ ([.LD .x5 .x10 (128 : BitVec 12), .LI .x6 (-1 : Word)],
     .beq .x5 .x6),
    ([.LI .x6 (8 : Word)], .bltu .x6 .x5) ]

/-- Static facts. -/
def spncStatic (rec : Word) (bs : List (BitVec 8)) : Prop :=
  144 ≤ bs.length ∧ rec.toNat + 144 < 2 ^ 64

/-- Cascade invariant. -/
def spncInv (rec : Word) (bs : List (BitVec 8)) : Nat → Reach
  | 0 => fun rf _ A => rf.get .x10 = rec ∧ spncStatic rec bs
      ∧ A = empAssertion
  | 1 => fun rf _ A => rf.get .x10 = rec ∧ rf.get .x5 = spncLen bs ∧
      spncLen bs ≠ (-1 : Word) ∧ spncStatic rec bs ∧ A = empAssertion
  | _ => fun rf _ A => rf.get .x10 = rec ∧ rf.get .x5 = spncLen bs ∧
      ¬ spncSkip bs ∧ spncStatic rec bs ∧ A = empAssertion

/-- Bad-entry states. -/
def spncBad (_rec : Word) (bs : List (BitVec 8)) : Reach :=
  fun _ _ A => spncSkip bs ∧ A = empAssertion

/-- Loop invariant: after `i` bytes, `x28` holds their BE accumulation. -/
def spncLInv (rec : Word) (bs : List (BitVec 8)) (i : Nat) : Reach :=
  fun rf _ A =>
    rf.get .x10 = rec ∧
    rf.get .x7 = rec + BitVec.ofNat 64 (136 + i) ∧
    rf.get .x28 = beAcc (((bs.drop 136).take (spncLen bs).toNat).take i) ∧
    rf.get .x29 = BitVec.ofNat 64 ((spncLen bs).toNat - i) ∧
    i ≤ (spncLen bs).toNat ∧ (spncLen bs).toNat ≤ 8 ∧
    ¬ spncSkip bs ∧ spncStatic rec bs ∧ A = empAssertion

/-- An `LD` that misses the writable window reads the read-only region. -/
theorem execInstrRF_ld_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs)
      = (rf.set rd (ro.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- In-bounds `getD` is `getElem`. -/
theorem getD_eq_getElem' (l : List (BitVec 8)) (i : Nat)
    (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some]

/-- `beAcc` step, `getD` form. -/
theorem beAcc_take_succ_getD (bytes : List (BitVec 8)) (i : Nat)
    (h : i < bytes.length) :
    beAcc (bytes.take (i + 1))
      = (beAcc (bytes.take i) <<< (8 : Nat))
        ||| (bytes.getD i 0).zeroExtend 64 := by
  rw [beAcc_take_succ bytes i h, getD_eq_getElem' bytes i h]

section Deriv

variable (rec : Word) (bs : List (BitVec 8))

local infix:36 " ⤳ " => DCode (Region.mk rec bs) RwRegion.empty

/-- Nothing fits in the empty writable window. -/
theorem spnc_no_rw (ws : List (BitVec 8)) (hlen : ws.length = 0)
    (a : Word) (n : Nat) (hn : 0 < n) :
    ¬ inRw RwRegion.empty.base ws a n := by
  unfold inRw
  omega

/-- The post-nonce byte window. -/
def spncBytes : List (BitVec 8) :=
  (bs.drop 136).take (spncLen bs).toNat

/-- The loop body. -/
def spncStepBlock : List Instr :=
  [ .SLLI .x28 .x28 (8 : BitVec 6), .LBU .x30 .x7 (0 : BitVec 12),
    .OR .x28 .x28 .x30, .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12) ]

/-- Register file after one accumulate trip (given the loaded byte). -/
def spncStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x28 (rf.get .x28 <<< (8 : Nat))
  let r2 := r1.set .x30 (b.zeroExtend 64)
  let r3 := r2.set .x28 (r2.get .x28 ||| r2.get .x30)
  let r4 := r3.set .x7 (r3.get .x7 + signExtend12 (1 : BitVec 12))
  r4.set .x29 (r4.get .x29 + signExtend12 (-1 : BitVec 12))

theorem spncStepRf_get_x10 (rf : RegFile) (b : BitVec 8) :
    (spncStepRf rf b).get .x10 = rf.get .x10 := by
  unfold spncStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28)]

theorem spncStepRf_get_x7 (rf : RegFile) (b : BitVec 8) :
    (spncStepRf rf b).get .x7
      = rf.get .x7 + signExtend12 (1 : BitVec 12) := by
  unfold spncStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]

theorem spncStepRf_get_x28 (rf : RegFile) (b : BitVec 8) :
    (spncStepRf rf b).get .x28
      = (rf.get .x28 <<< (8 : Nat)) ||| b.zeroExtend 64 := by
  unfold spncStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x7),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_self _ _ _ (by decide)]

theorem spncStepRf_get_x29 (rf : RegFile) (b : BitVec 8) :
    (spncStepRf rf b).get .x29
      = rf.get .x29 + signExtend12 (-1 : BitVec 12) := by
  unfold spncStepRf
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x29 ≠ .x28)]

/-- Engine: one accumulate trip loads byte `136 + i` and shifts it in. -/
theorem spnc_step_engine (i : Nat) (rf : RegFile) (ws : List (BitVec 8))
    (h7 : rf.get .x7 = rec + BitVec.ofNat 64 (136 + i))
    (_hi : 136 + i + 1 ≤ bs.length)
    (hrec : rec.toNat + 144 < 2 ^ 64) (_hi8 : i < 8)
    (hws : ws.length = 0) :
    execBlock (Region.mk rec bs) RwRegion.empty.base rf ws spncStepBlock
      = (spncStepRf rf (bs.getD (136 + i) 0), ws) := by
  have haddr : (rf.set .x28 (rf.get .x28 <<< (8 : BitVec 6).toNat)).get .x7
      + signExtend12 (0 : BitVec 12) = rec + BitVec.ofNat 64 (136 + i) := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), h7,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    simp
  rw [show spncStepBlock =
      [.SLLI .x28 .x28 (8 : BitVec 6), .LBU .x30 .x7 (0 : BitVec 12),
       .OR .x28 .x28 .x30, .ADDI .x7 .x7 (1 : BitVec 12),
       .ADDI .x29 .x29 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _
    (by rw [haddr]; exact spnc_no_rw ws hws _ 1 (by omega))]
  dsimp only
  rw [show Region.byteAt (Region.mk rec bs) _ = bs.getD (136 + i) 0 from by
    rw [haddr]
    show bs.getD ((rec + BitVec.ofNat 64 (136 + i) - rec).toNat) 0 = _
    rw [show (rec + BitVec.ofNat 64 (136 + i) - rec).toNat = 136 + i from
      by bv_omega]]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  rfl

/-- Proof-first nonce-consistency check. -/
def spncDeriv :
    DCode (Region.mk rec bs) RwRegion.empty
      (fun rf _ A => rf.get .x10 = rec ∧ spncStatic rec bs
        ∧ A = empAssertion)
      (fun rf _ A => rf.get .x10 = spncOut bs ∧ A = empAssertion) :=
  DCode.dretCascade "skip" spncStages (spncInv rec bs) (spncBad rec bs)
    (fun _ _ _ h => h)
    ⟨⟨by decide,
      (fun _ rf ws A hlen hpre => by
        obtain ⟨h10, ⟨hbs, hrec⟩, hA⟩ := hpre
        have hws0 : ws.length = 0 := hlen
        refine ⟨?_, trivial, trivial⟩
        simp only [loadSem]
        rw [if_neg (spnc_no_rw ws hws0 _ 8 (by omega))]
        rw [show rf.get .x10 + signExtend12 (128 : BitVec 12)
            = rec + (128 : Word) from by
          rw [h10, show signExtend12 (128 : BitVec 12) = (128 : Word)
            from by decide]]
        show 8 ∣ (rec + (128 : Word) - rec).toNat
          ∧ (rec + (128 : Word) - rec).toNat + 8 ≤ bs.length
        rw [show (rec + (128 : Word) - rec).toNat = 128 from by bv_omega]
        exact ⟨by omega, by omega⟩),
      (by
        intro rfx wsx A hstep hnc
        obtain ⟨rf0, ws0, hlen, ⟨h10, hst, hA⟩, hrf, hws⟩ := hstep
        subst hrf
        subst hws
        have hws00 : wsx.length = 0 := hlen
        simp only [execBlock_cons, execBlock_nil] at hnc ⊢
        rw [execInstrRF_ld_ro _ _ _ _ _ _ _
          (spnc_no_rw wsx hws00 _ 8 (by omega))] at hnc ⊢
        dsimp only [execInstrRF, aluSem] at hnc ⊢
        simp only [Cond.holds] at hnc
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
          RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_self _ _ _ (by decide)] at hnc
        have hval : Region.dwordAt (Region.mk rec bs)
            (rf0.get .x10 + signExtend12 (128 : BitVec 12))
            = spncLen bs := by
          rw [h10, show signExtend12 (128 : BitVec 12) = (128 : Word)
            from by decide]
          show packBytes ((bs.drop (rec + (128 : Word) - rec).toNat).take 8)
            = spncLen bs
          rw [show (rec + (128 : Word) - rec).toNat = 128 from by
            obtain ⟨hbs, hrec⟩ := hst
            bv_omega]
          rfl
        rw [hval] at hnc
        refine ⟨?_, ?_, hnc, hst, hA⟩
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), h10]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
            RegFile.get_set_self _ _ _ (by decide), hval]),
      (by
        intro rfx wsx A hstep hc
        obtain ⟨rf0, ws0, hlen, ⟨h10, hst, hA⟩, hrf, hws⟩ := hstep
        subst hrf
        subst hws
        have hws00 : wsx.length = 0 := hlen
        simp only [execBlock_cons, execBlock_nil] at hc
        rw [execInstrRF_ld_ro _ _ _ _ _ _ _
          (spnc_no_rw wsx hws00 _ 8 (by omega))] at hc
        dsimp only [execInstrRF, aluSem] at hc
        simp only [Cond.holds] at hc
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
          RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_self _ _ _ (by decide)] at hc
        have hval : Region.dwordAt (Region.mk rec bs)
            (rf0.get .x10 + signExtend12 (128 : BitVec 12))
            = spncLen bs := by
          rw [h10, show signExtend12 (128 : BitVec 12) = (128 : Word)
            from by decide]
          show packBytes ((bs.drop (rec + (128 : Word) - rec).toNat).take 8)
            = spncLen bs
          rw [show (rec + (128 : Word) - rec).toNat = 128 from by
            obtain ⟨hbs, hrec⟩ := hst
            bv_omega]
          rfl
        rw [hval] at hc
        exact ⟨Or.inl hc, hA⟩)⟩,
     ⟨by decide,
      (fun h => absurd h (by decide)),
      (by
        intro rfx wsx A hstep hnc
        obtain ⟨rf0, ws0, hlen, ⟨h10, h5, hne, hst, hA⟩, hrf, hws⟩ := hstep
        subst hrf
        subst hws
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hnc ⊢
        simp only [Cond.holds] at hnc
        rw [RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), h5] at hnc
        refine ⟨?_, ?_, ?_, hst, hA⟩
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6), h10]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), h5]
        · rintro (habs | hgt)
          · exact hne habs
          · exact hnc hgt),
      (by
        intro rfx wsx A hstep hc
        obtain ⟨rf0, ws0, hlen, ⟨h10, h5, hne, hst, hA⟩, hrf, hws⟩ := hstep
        subst hrf
        subst hws
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hc
        simp only [Cond.holds] at hc
        rw [RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), h5] at hc
        exact ⟨Or.inr hc, hA⟩)⟩,
     trivial⟩
    (calc (fun rf ws A => spncInv rec bs 2 rf ws A : Reach)
      _ ⤳ (fun rf ws A => spncLInv rec bs 0 rf ws A : Reach) :=
        DCode.block "init"
          [.ADDI .x7 .x10 (136 : BitVec 12), .LI .x28 (0 : Word),
           .MV .x29 .x5]
          (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨h10, h5, hns, hst, hA⟩
            have hn8 : (spncLen bs).toNat ≤ 8 := by
              have hle : ¬ (BitVec.ult (8 : Word) (spncLen bs) = true) :=
                fun h => hns (Or.inr h)
              simp only [BitVec.ult, decide_eq_true_eq] at hle
              bv_omega
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem,
              spncLInv]
            refine ⟨?_, ?_, ?_, ?_, by omega, hn8, hns, hst, hA⟩
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x29),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x28),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
                h10]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
                RegFile.get_set_self _ _ _ (by decide), h10,
                show signExtend12 (136 : BitVec 12) = (136 : Word) from
                  by decide]
              rfl
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
                RegFile.get_set_self _ _ _ (by decide)]
              rfl
            · rw [RegFile.get_set_self _ _ _ (by decide),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7), h5]
              bv_omega)
      _ ⤳ (fun rf ws A => (∃ i, i ≤ 8 ∧ spncLInv rec bs i rf ws A)
            ∧ ¬ (Cond.bne .x29 .x0).holds rf : Reach) :=
        DCode.dwhile "acc" (.bne .x29 .x0) 8 (spncLInv rec bs)
          (fun _ _ _ h => h)
          (fun i =>
            DCode.block "byte" spncStepBlock
              (by decide)
              (fun _ rf ws A hlen hpre => by
                obtain ⟨hi8, ⟨h10, h7, h28, h29, hile, hn8, hns,
                  ⟨hbs, hrec⟩, hA⟩, hg⟩ := hpre
                have hws0 : ws.length = 0 := hlen
                have hin : i < (spncLen bs).toNat := by
                  simp only [Cond.holds, RegFile.get_x0, ne_eq] at hg
                  rw [h29] at hg
                  bv_omega
                refine ⟨trivial, ?_, trivial, trivial, trivial, trivial⟩
                dsimp only [execInstrRF, aluSem]
                simp only [loadSem]
                rw [if_neg (by
                  rw [show (rf.set .x28 _).get .x7
                      + signExtend12 (0 : BitVec 12)
                      = rec + BitVec.ofNat 64 (136 + i) from by
                    rw [RegFile.get_set_ne _ _ _ _
                        (by decide : Reg.x7 ≠ .x28), h7,
                      show signExtend12 (0 : BitVec 12) = (0 : Word) from
                        by decide]
                    simp]
                  exact spnc_no_rw ws hws0 _ 1 (by omega))]
                rw [show (rf.set .x28 _).get .x7
                    + signExtend12 (0 : BitVec 12)
                    = rec + BitVec.ofNat 64 (136 + i) from by
                  rw [RegFile.get_set_ne _ _ _ _
                      (by decide : Reg.x7 ≠ .x28), h7,
                    show signExtend12 (0 : BitVec 12) = (0 : Word) from
                      by decide]
                  simp]
                show 1 ∣ (rec + BitVec.ofNat 64 (136 + i) - rec).toNat
                  ∧ (rec + BitVec.ofNat 64 (136 + i) - rec).toNat + 1
                    ≤ bs.length
                rw [show (rec + BitVec.ofNat 64 (136 + i) - rec).toNat
                    = 136 + i from by bv_omega]
                exact ⟨Nat.one_dvd _, by omega⟩)
              (fun rf ws A hlen hpre => by
                obtain ⟨hi8, ⟨h10, h7, h28, h29, hile, hn8, hns,
                  ⟨hbs, hrec⟩, hA⟩, hg⟩ := hpre
                have hws0 : ws.length = 0 := hlen
                have hin : i < (spncLen bs).toNat := by
                  simp only [Cond.holds, RegFile.get_x0, ne_eq] at hg
                  rw [h29] at hg
                  bv_omega
                rw [spnc_step_engine rec bs i rf ws h7 (by omega) hrec
                  (by omega) hws0]
                simp only [spncLInv]
                refine ⟨?_, ?_, ?_, ?_, by omega, hn8, hns, ⟨hbs, hrec⟩,
                  hA⟩
                · rw [spncStepRf_get_x10, h10]
                · rw [spncStepRf_get_x7, h7,
                    show signExtend12 (1 : BitVec 12) = (1 : Word) from
                      by decide]
                  bv_omega
                · rw [spncStepRf_get_x28, h28]
                  show (beAcc ((spncBytes bs).take i) <<< (8 : Nat))
                      ||| (bs.getD (136 + i) 0).zeroExtend 64
                    = beAcc ((spncBytes bs).take (i + 1))
                  rw [beAcc_take_succ_getD (spncBytes bs) i
                    (by simp only [spncBytes, List.length_take,
                      List.length_drop]; omega)]
                  rw [show (spncBytes bs).getD i 0
                      = bs.getD (136 + i) 0 from by
                    rw [getD_eq_getElem' (spncBytes bs) i
                        (by simp only [spncBytes, List.length_take,
                          List.length_drop]; omega),
                      getD_eq_getElem' bs (136 + i) (by omega)]
                    simp only [spncBytes, List.getElem_take,
                      List.getElem_drop]]
                · rw [spncStepRf_get_x29, h29,
                    show signExtend12 (-1 : BitVec 12) = (-1 : Word) from
                      by decide]
                  bv_omega))
          (fun rf ws A h => by
            obtain ⟨-, -, -, h29, hile, hn8, -⟩ := h
            simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
            rw [h29, show (spncLen bs).toNat - 8 = 0 from by omega]
            rfl)
      _ ⤳ (fun rf ws A => rf.get .x10 = rec
            ∧ rf.get .x28 = beAcc (spncBytes bs)
            ∧ ¬ spncSkip bs ∧ spncStatic rec bs ∧ A = empAssertion
            : Reach) :=
        DCode.pure "accdone"
          (by
            rintro rf ws A ⟨⟨i, hile, h10, h7, h28, h29, hin, hn8, hns,
              hst, hA⟩, hc⟩
            simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hc
            have hieq : i = (spncLen bs).toNat := by
              rw [h29] at hc
              bv_omega
            subst hieq
            refine ⟨h10, ?_, hns, hst, hA⟩
            rw [h28, List.take_of_length_le (by
              simp only [List.length_take, List.length_drop]
              omega)]
            rfl)
      _ ⤳ (fun rf ws A => rf.get .x28 = beAcc (spncBytes bs)
            ∧ rf.get .x29 = spncPre bs + 1
            ∧ ¬ spncSkip bs ∧ A = empAssertion : Reach) :=
        DCode.block "cmp"
          [.LD .x29 .x10 (80 : BitVec 12), .ADDI .x29 .x29 (1 : BitVec 12)]
          (by decide)
          (fun _ rf ws A hlen hpre => by
            obtain ⟨h10, h28, hns, ⟨hbs, hrec⟩, hA⟩ := hpre
            have hws0 : ws.length = 0 := hlen
            refine ⟨?_, trivial, trivial⟩
            simp only [loadSem]
            rw [if_neg (spnc_no_rw ws hws0 _ 8 (by omega))]
            rw [show rf.get .x10 + signExtend12 (80 : BitVec 12)
                = rec + (80 : Word) from by
              rw [h10, show signExtend12 (80 : BitVec 12) = (80 : Word)
                from by decide]]
            show 8 ∣ (rec + (80 : Word) - rec).toNat
              ∧ (rec + (80 : Word) - rec).toNat + 8 ≤ bs.length
            rw [show (rec + (80 : Word) - rec).toNat = 80 from by
              bv_omega]
            exact ⟨by omega, by omega⟩)
          (by
            rintro rf ws A _ ⟨h10, h28, hns, ⟨hbs, hrec⟩, hA⟩
            simp only [execBlock_cons, execBlock_nil]
            rw [execInstrRF_ld_ro _ _ _ _ _ _ _ (by
              intro hin
              unfold inRw at hin
              have : ws.length = 0 := ‹ws.length = _›
              omega)]
            dsimp only [execInstrRF, aluSem]
            have hval : Region.dwordAt (Region.mk rec bs)
                (rf.get .x10 + signExtend12 (80 : BitVec 12))
                = spncPre bs := by
              rw [h10, show signExtend12 (80 : BitVec 12) = (80 : Word)
                from by decide]
              show packBytes ((bs.drop (rec + (80 : Word)
                - rec).toNat).take 8) = spncPre bs
              rw [show (rec + (80 : Word) - rec).toNat = 80 from by
                bv_omega]
              rfl
            refine ⟨?_, ?_, hns, hA⟩
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
                h28]
            · rw [RegFile.get_set_self _ _ _ (by decide),
                RegFile.get_set_self _ _ _ (by decide), hval,
                show signExtend12 (1 : BitVec 12) = (1 : Word) from
                  by decide])
      _ ⤳ (fun rf _ A => rf.get .x10 = spncOut bs ∧ A = empAssertion
            : Reach) :=
        DCode.dretIf "eq" (.beq .x28 .x29)
          (DCode.seq
            (DCode.block "eq0" [.LI .x10 (0 : Word)] (by decide)
              (fun h => absurd h (by decide))
              (by
                rintro rf ws A _ ⟨⟨h28, h29, hns, hA⟩, hc⟩
                simp only [Cond.holds, h28, h29] at hc
                simp only [execBlock_cons, execBlock_nil, execInstrRF,
                  aluSem]
                refine ⟨?_, hA⟩
                rw [RegFile.get_set_self _ _ _ (by decide), spncOut,
                  if_neg hns,
                  if_pos (show beAcc ((bs.drop 136).take
                      (spncLen bs).toNat) = spncPre bs + 1 from hc)]))
            (DCode.retJalr "eqr"))
          (DCode.seq
            (DCode.block "ne1" [.LI .x10 (1 : Word)] (by decide)
              (fun h => absurd h (by decide))
              (by
                rintro rf ws A _ ⟨⟨h28, h29, hns, hA⟩, hc⟩
                simp only [Cond.holds, h28, h29] at hc
                simp only [execBlock_cons, execBlock_nil, execInstrRF,
                  aluSem]
                refine ⟨?_, hA⟩
                rw [RegFile.get_set_self _ _ _ (by decide), spncOut,
                  if_neg hns,
                  if_neg (show ¬ (beAcc ((bs.drop 136).take
                      (spncLen bs).toNat) = spncPre bs + 1) from hc)]))
            (DCode.retJalr "ner")))
    (DCode.seq
      (DCode.block "skip2" [.LI .x10 (2 : Word)] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨hskip, hA⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          refine ⟨?_, hA⟩
          rw [RegFile.get_set_self _ _ _ (by decide), spncOut,
            if_pos hskip]))
      (DCode.retJalr "skipr"))

/-- The generated multi-exit spec: the `ra`-framed triple at any base and
    aligned return address — `a0` ends as the consistency verdict
    (0 consistent / 1 mismatch / 2 skip). -/
theorem spnc_retSpec (hreg : (Region.mk rec bs).wf) (base ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (spncDeriv rec bs).stmt.steps base ret
      (CodeReq.ofProg base ((spncDeriv rec bs).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk rec bs) RwRegion.empty
          (fun rf _ A => rf.get .x10 = rec ∧ spncStatic rec bs
            ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk rec bs) RwRegion.empty
          (fun rf _ A => rf.get .x10 = spncOut bs ∧ A = empAssertion)) :=
  DCode.retSpec (spncDeriv rec bs) base ret hreg RwRegion.empty_wf
    halign (fun _ _ h => h)

end Deriv

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- The generated code (return tails are IN the code — no epilogue). -/
def spnc_prog : Program := (spncDeriv 0 []).stmt.flatten 0

-- Byte-identity with the already-converted deployed program (whose
-- emitted string carries its own rfl drift theorem).
#guard (spnc_prog : List Instr)
    == (Codegen.senderPostNonceConsistent_prog : List Instr)

#guard spnc_prog.length = 24

-- The code does not depend on the ghost arguments (sampled).
#guard (((spncDeriv 5 [1, 2]).stmt.flatten 0) : List Instr)
    == (spnc_prog : List Instr)

end SenderPostNonceConsistentSAsm

end EvmAsm.Codegen
