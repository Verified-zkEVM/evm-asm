/-
  EvmAsm.Codegen.Programs.ModexpIszeroSAsm

  Proof-first (DCode) port of `modexp_iszero` — the modexp backend's
  limb-array zero test (`a0` = limb pointer, `a1` = n_limbs; returns
  `a0 = 1` iff all `n` little-endian dword limbs are zero).

  First user of the tail-swapped return-terminating break loop
  (`dretWhileBreakSwap` / `Stmt.retWhileBreakSwap`): the scan's break
  branch (a nonzero limb) exits to the NEAR tail (`li a0,0; ret`) and
  the guard exhaustion (all limbs scanned) jumps PAST it to the far
  tail (`li a0,1; ret`) — the layout `retWhileBreak` cannot express.
  Byte-identity with the previously hand-written routine in
  `ModexpBackend.lean` verified by assemble+cmp; the emitted slice is
  now `emitProgram` of the generated program.
-/

import EvmAsm.Rv64.SAsm.Deriv

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

namespace ModexpIszeroSAsm

/-! ## The routine's semantics -/

/-- The `k`-limb prefix is all zero (limb `j` = the dword at `ptr + 8j`). -/
def mizZero (ptr : Word) (bs : List (BitVec 8)) (k : Nat) : Prop :=
  ∀ j, j < k →
    (Region.mk ptr bs).dwordAt (ptr + BitVec.ofNat 64 (8 * j)) = 0

instance (ptr : Word) (bs : List (BitVec 8)) (k : Nat) :
    Decidable (mizZero ptr bs k) := by
  unfold mizZero
  infer_instance

/-- The returned flag: 1 iff all `n` limbs are zero. -/
def mizOut (ptr : Word) (bs : List (BitVec 8)) (n : Nat) : Word :=
  if mizZero ptr bs n then 1 else 0

/-- Facts the loop never touches: the two argument registers and the
    (ghost) buffer bounds.  `n ≤ 256` is the deployed
    `modexpBnMaxLimbs` cap (all callers pass `ceil(len/8)` against
    2048-byte buffers). -/
def mizStatic (ptr : Word) (bs : List (BitVec 8)) (n : Nat)
    (rf : RegFile) : Prop :=
  rf.get .x10 = ptr ∧ rf.get .x11 = BitVec.ofNat 64 n ∧
  n ≤ 256 ∧ 8 * n ≤ bs.length

/-- Loop invariant at the i-th header evaluation: `t0` counts limbs,
    everything before it was zero. -/
def mizInv (ptr : Word) (bs : List (BitVec 8)) (n : Nat) : Nat → Reach :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧ i ≤ n ∧
    mizStatic ptr bs n rf ∧ mizZero ptr bs i ∧ A = empAssertion

/-- Mid-states at the break test: `t2` holds limb `i`. -/
def mizMid (ptr : Word) (bs : List (BitVec 8)) (n : Nat) : Nat → Reach :=
  fun i rf _ A =>
    rf.get .x5 = BitVec.ofNat 64 i ∧ i < n ∧
    mizStatic ptr bs n rf ∧ mizZero ptr bs i ∧
    rf.get .x7 = (Region.mk ptr bs).dwordAt (ptr + BitVec.ofNat 64 (8 * i)) ∧
    A = empAssertion

/-! ## Local helpers -/

/-- An empty writable window admits no in-window access. -/
theorem miz_no_rw (ws : List (BitVec 8)) (h0 : ws.length = 0)
    (a : Word) (n : Nat) (hn : 0 < n) :
    ¬ inRw RwRegion.empty.base ws a n := by
  unfold inRw
  omega

/-- An `LD` that misses the writable window reads the read-only region. -/
theorem execInstrRF_ld_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs)
      = (rf.set rd (ro.dwordAt (rf.get rs1 + signExtend12 ofs)), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- `t0 <<< 3` is the byte offset of limb `t0`. -/
theorem miz_shift (i : Nat) (_hi : i ≤ 256) :
    BitVec.ofNat 64 i <<< (3 : Nat) = BitVec.ofNat 64 (8 * i) := by
  bv_omega

/-! ## The derivation -/

/-- Proof-first limb-array zero scan: guard `t0 ≠ a1` keeps scanning,
    a nonzero limb breaks to the near `0` tail, exhaustion jumps to the
    far `1` tail. -/
def mizDeriv (ptr : Word) (bs : List (BitVec 8)) (n : Nat) :
    DCode (Region.mk ptr bs) RwRegion.empty
      (fun rf _ A => mizStatic ptr bs n rf ∧ A = empAssertion)
      (fun rf _ A => rf.get .x10 = mizOut ptr bs n ∧ A = empAssertion) :=
  DCode.seq
    (DCode.block "init" [.LI .x5 (0 : Word)] (by decide)
      (fun h => absurd h (by decide))
      (by
        rintro rf ws A hlen ⟨⟨h10, h11, hn, hbs⟩, hA⟩
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
        refine ⟨?_, Nat.zero_le n, ⟨?_, ?_, hn, hbs⟩, ?_, hA⟩
        · rw [RegFile.get_set_self _ _ _ (by decide)]
          rfl
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), h10]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), h11]
        · intro j hj
          omega))
    (DCode.dretWhileBreakSwap "scan" (.bne .x5 .x11) 256
      (mizInv ptr bs n) (mizMid ptr bs n) (.bne .x7 .x0)
      (fun _ _ _ h => h)
      (fun i =>
        DCode.block "load"
          [.SLLI .x6 .x5 (3 : BitVec 6), .ADD .x7 .x10 .x6,
           .LD .x7 .x7 (0 : BitVec 12)]
          (by decide)
          (fun _ rf ws A hlen hpre => by
            obtain ⟨hi, ⟨h5, hile, ⟨h10, h11, hn, hbs⟩, hz, hA⟩, hg⟩ := hpre
            have hws0 : ws.length = 0 := hlen
            have hin : i < n := by
              simp only [Cond.holds, ne_eq] at hg
              rw [h5, h11] at hg
              rcases Nat.lt_or_ge i n with h | h
              · exact h
              · exact absurd (by omega : i = n) (fun he => hg (he ▸ rfl))
            refine ⟨trivial, trivial, ?_, trivial⟩
            dsimp only [execInstrRF, aluSem, loadSem]
            have haddr : ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                  ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                    + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6)).get .x7
                  + signExtend12 (0 : BitVec 12)
                = ptr + BitVec.ofNat 64 (8 * i) := by
              rw [RegFile.get_set_self _ _ _ (by decide),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
                RegFile.get_set_self _ _ _ (by decide),
                h10, h5,
                show BitVec.toNat (3 : BitVec 6) = 3 from by decide,
                miz_shift i (by omega),
                show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
              simp
            have hno : ¬ inRw RwRegion.empty.base ws
                (((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                    ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                      + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6)).get .x7
                  + signExtend12 (0 : BitVec 12)) 8 :=
              miz_no_rw ws hws0 _ 8 (by omega)
            show if inRw RwRegion.empty.base ws
                  (((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                      ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                        + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6)).get .x7
                    + signExtend12 (0 : BitVec 12)) 8
                then (Region.mk RwRegion.empty.base ws).loadOk
                  (((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                      ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                        + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6)).get .x7
                    + signExtend12 (0 : BitVec 12)) 8
                else (Region.mk ptr bs).loadOk
                  (((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                      ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                        + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6)).get .x7
                    + signExtend12 (0 : BitVec 12)) 8
            rw [if_neg hno, haddr]
            show 8 ∣ (ptr + BitVec.ofNat 64 (8 * i) - ptr).toNat
              ∧ (ptr + BitVec.ofNat 64 (8 * i) - ptr).toNat + 8 ≤ bs.length
            rw [show (ptr + BitVec.ofNat 64 (8 * i) - ptr).toNat = 8 * i from by
              bv_omega]
            exact ⟨⟨i, rfl⟩, by omega⟩)
          (by
            rintro rf ws A hlen ⟨_hi, ⟨h5, hile, ⟨h10, h11, hn, hbs⟩, hz, hA⟩,
              hg⟩
            have hws0 : ws.length = 0 := hlen
            have hin : i < n := by
              simp only [Cond.holds, ne_eq] at hg
              rw [h5, h11] at hg
              rcases Nat.lt_or_ge i n with h | h
              · exact h
              · exact absurd (by omega : i = n) (fun he => hg (he ▸ rfl))
            have haddr : ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                  ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                    + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6)).get .x7
                  + signExtend12 (0 : BitVec 12)
                = ptr + BitVec.ofNat 64 (8 * i) := by
              rw [RegFile.get_set_self _ _ _ (by decide),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
                RegFile.get_set_self _ _ _ (by decide),
                h10, h5,
                show BitVec.toNat (3 : BitVec 6) = 3 from by decide,
                miz_shift i (by omega),
                show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
              simp
            have hexec : execBlock (Region.mk ptr bs) RwRegion.empty.base rf ws
                  [.SLLI .x6 .x5 (3 : BitVec 6), .ADD .x7 .x10 .x6,
                   .LD .x7 .x7 (0 : BitVec 12)]
                = execInstrRF (Region.mk ptr bs) RwRegion.empty.base
                    ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).set .x7
                      ((rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x10
                        + (rf.set .x6 (rf.get .x5 <<< BitVec.toNat (3 : BitVec 6))).get .x6))
                    ws (.LD .x7 .x7 (0 : BitVec 12)) := rfl
            rw [hexec, execInstrRF_ld_ro _ _ _ _ _ _ _
              (haddr ▸ miz_no_rw ws hws0 (ptr + BitVec.ofNat 64 (8 * i)) 8
                (by omega)), haddr]
            refine ⟨?_, hin, ⟨?_, ?_, hn, hbs⟩, hz, ?_, hA⟩
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6), h5]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x7),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6), h10]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
                RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), h11]
            · rw [RegFile.get_set_self _ _ _ (by decide)]))
      (fun i =>
        DCode.block "step" [.ADDI .x5 .x5 (1 : BitVec 12)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A hlen
              ⟨hi, ⟨h5, hin, ⟨h10, h11, hn, hbs⟩, hz, h7, hA⟩, hnbr⟩
            simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hnbr
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            refine ⟨?_, by omega, ⟨?_, ?_, hn, hbs⟩, ?_, hA⟩
            · rw [RegFile.get_set_self _ _ _ (by decide), h5,
                show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
              bv_omega
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), h10]
            · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), h11]
            · intro j hj
              rcases Nat.lt_or_ge j i with h | h
              · exact hz j h
              · have : j = i := by omega
                subst this
                rw [← h7]
                exact hnbr))
      (by
        rintro rf ws A ⟨h5, hile, ⟨h10, h11, hn, hbs⟩, hz, hA⟩
        simp only [Cond.holds, ne_eq, not_not]
        have : n = 256 := by omega
        subst this
        rw [h5, h11])
      (DCode.seq
        (DCode.block "yes" [.LI .x10 (1 : Word)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨⟨i, hile, h5, hin, ⟨h10, h11, hn, hbs⟩, hz, hA⟩,
              hng⟩
            simp only [Cond.holds, ne_eq, not_not] at hng
            have hieq : i = n := by
              rw [h5, h11] at hng
              bv_omega
            subst hieq
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            refine ⟨?_, hA⟩
            rw [RegFile.get_set_self _ _ _ (by decide), mizOut, if_pos hz]))
        (DCode.retJalr "yret"))
      (DCode.seq
        (DCode.block "no" [.LI .x10 (0 : Word)] (by decide)
          (fun h => absurd h (by decide))
          (by
            rintro rf ws A _ ⟨⟨i, hin, h5, hilt, ⟨h10, h11, hn, hbs⟩, hz, h7,
              hA⟩, hbr⟩
            simp only [Cond.holds, RegFile.get_x0, ne_eq] at hbr
            simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
            refine ⟨?_, hA⟩
            rw [RegFile.get_set_self _ _ _ (by decide), mizOut,
              if_neg (fun hall => hbr (h7.trans (hall i hilt)))]))
        (DCode.retJalr "nret")))

/-! ## The generated code and spec -/

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- The generated code (both return tails are IN the code). -/
def modexpIszero_prog : Program :=
  (mizDeriv 0 [] 0).stmt.flatten 0

-- Pinned instruction sequence (build-time evaluation): byte-identical to
-- the previously hand-written routine.
#guard (modexpIszero_prog : List Instr) ==
    [ .LI .x5 (0 : Word),
      .BEQ .x5 .x11 (36 : BitVec 13),
      .SLLI .x6 .x5 (3 : BitVec 6),
      .ADD .x7 .x10 .x6,
      .LD .x7 .x7 (0 : BitVec 12),
      .BNE .x7 .x0 (12 : BitVec 13),
      .ADDI .x5 .x5 (1 : BitVec 12),
      .JAL .x0 (-24 : BitVec 21),
      .LI .x10 (0 : Word),
      .JALR .x0 .x1 (0 : BitVec 12),
      .LI .x10 (1 : Word),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard modexpIszero_prog.length = 12

-- The code does not depend on the ghost arguments (sampled).
#guard (((mizDeriv 8 [0, 0] 3).stmt.flatten 0) : List Instr)
    == (modexpIszero_prog : List Instr)

/-- The generated multi-exit spec: the `ra`-framed triple at any base and
    aligned return address — `a0` ends as the all-limbs-zero flag. -/
theorem modexpIszero_retSpec (ptr : Word) (bs : List (BitVec 8)) (n : Nat)
    (base ret : Word)
    (hwf : (Region.mk ptr bs).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (mizDeriv ptr bs n).stmt.steps base ret
      (CodeReq.ofProg base ((mizDeriv ptr bs n).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk ptr bs) RwRegion.empty
          (fun rf _ A => mizStatic ptr bs n rf ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk ptr bs) RwRegion.empty
          (fun rf _ A => rf.get .x10 = mizOut ptr bs n
            ∧ A = empAssertion)) :=
  DCode.retSpec (mizDeriv ptr bs n) base ret
    hwf RwRegion.empty_wf halign (fun _ _ h => h)

end ModexpIszeroSAsm

end EvmAsm.Codegen
