/-
  EvmAsm.Codegen.Programs.EddMemcpySAsm

  Proof-first (DCode) port of `edd_memcpy` — the deposit-request
  extractor's byte-wise copy leaf (`a0` = src, `a1` = dst, `a2` = len).

  First DCode consumer that WRITES the writable window: the loop body
  stores one byte per trip (`sb`), so the derivation's invariant tracks
  the window contents (`take i` of the source spliced over the original
  window) and the store VCs discharge against the window bounds; the
  source is read via the read-only region, with the load VCs discharged
  from a caller-supplied disjointness fact.  Byte-identity with the
  hand-written routine in `ExtractDepositData.lean` verified by
  assemble+cmp; the emitted slice is now `emitProgram` of the generated
  program.
-/

import EvmAsm.Rv64.SAsm.Deriv
import EvmAsm.Rv64.SAsm.MultiDword

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

namespace EddMemcpySAsm

/-! ## The routine's semantics -/

/-- Facts the loop never disturbs: buffer bounds, no address wrap, and
    src/dst disjointness.  The deployed callers copy between disjoint
    scratch arenas, and that is now a THEOREM, not a docstring claim:
    `eddMemcpy_callsite_spec` in `ExtractDepositData.lean` discharges
    this whole conjunction from the concrete arena addresses at all five
    `extract_deposit_data` call sites (#12805). -/
def mcStatic (src dst : Word) (bs ws0 : List (BitVec 8)) (n : Nat) : Prop :=
  n ≤ bs.length ∧ ws0.length = n ∧ n < 2 ^ 32 ∧
  src.toNat + n < 2 ^ 64 ∧ dst.toNat + n < 2 ^ 64 ∧
  (src.toNat + n ≤ dst.toNat ∨ dst.toNat + n ≤ src.toNat)

/-- Loop invariant at the i-th guard evaluation: pointers advanced by
    `i`, count down by `i`, the window holds the copied prefix. -/
def mcInv (src dst : Word) (bs ws0 : List (BitVec 8)) (n : Nat) :
    Nat → Reach :=
  fun i rf ws A =>
    rf.get .x10 = src + BitVec.ofNat 64 i ∧
    rf.get .x11 = dst + BitVec.ofNat 64 i ∧
    rf.get .x12 = BitVec.ofNat 64 (n - i) ∧
    i ≤ n ∧ ws = bs.take i ++ ws0.drop i ∧ A = empAssertion

/-! ## Local helpers -/

/-- An `lbu` that misses the writable window reads the read-only region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd (BitVec.zeroExtend 64
          (ro.byteAt (rf.get rs1 + signExtend12 ofs))), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- `sb` stores one truncated byte into the window. -/
theorem execInstrRF_sb' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rs1 rs2 : Reg) (ofs : BitVec 12) :
    execInstrRF ro b rf ws (.SB rs1 rs2 ofs)
      = (rf, setBytes ws (rf.get rs1 + signExtend12 ofs - b).toNat
          [(rf.get rs2).truncate 8]) := rfl

theorem execInstrRF_addi' (ro : Region) (b : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrRF ro b rf ws (.ADDI rd rs1 imm)
      = (rf.set rd (rf.get rs1 + signExtend12 imm), ws) := rfl

/-- A load VC whose address misses the window is the read-only
    obligation. -/
theorem mc_vc (b : Word) (ws : List (BitVec 8)) (ro : Region) (a : Word)
    (n : Nat) (hno : ¬ inRw b ws a n) (h : ro.loadOk a n) :
    if inRw b ws a n
    then (Region.mk b ws).loadOk a n
    else ro.loadOk a n := by
  rw [if_neg hno]
  exact h

/-- In-bounds `getD` is `getElem`. -/
theorem getD_eq_getElem' (l : List (BitVec 8)) (i : Nat)
    (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    Option.getD_some]

/-- Writing source byte `i` at window slot `i` extends the copied
    prefix. -/
theorem mc_copy_step (bs ws0 : List (BitVec 8)) (n i : Nat)
    (hin : i < n) (hbs : n ≤ bs.length) (hw : ws0.length = n) :
    (bs.take i ++ ws0.drop i).set i (bs[i]'(by omega))
      = bs.take (i + 1) ++ ws0.drop (i + 1) := by
  apply List.ext_getElem
  · simp only [List.length_set, List.length_append, List.length_take,
      List.length_drop]
    omega
  · intro j h1 h2
    simp only [List.getElem_set, List.getElem_append, List.length_take,
      List.length_set, List.length_append, List.length_drop] at h1 h2 ⊢
    rcases Nat.lt_trichotomy j i with hj | hj | hj
    · rw [if_neg (by omega), dif_pos (by omega), dif_pos (by omega),
        List.getElem_take, List.getElem_take]
    · subst hj
      rw [if_pos rfl, dif_pos (by omega), List.getElem_take]
    · rw [if_neg (by omega), dif_neg (by omega), dif_neg (by omega),
        List.getElem_drop, List.getElem_drop]
      congr 1
      omega

/-! ## The derivation -/

/-- Proof-first byte copy: `while a2 ≠ 0 { *dst++ = *src++; a2-- }`. -/
def mcDeriv (src dst : Word) (bs ws0 : List (BitVec 8)) (n : Nat) :
    DCode (Region.mk src bs) (RwRegion.mk dst n)
      (fun rf ws A => rf.get .x10 = src ∧ rf.get .x11 = dst ∧
        rf.get .x12 = BitVec.ofNat 64 n ∧ ws = ws0 ∧
        mcStatic src dst bs ws0 n ∧ A = empAssertion)
      (fun _ ws A => ws = bs.take n ∧ mcStatic src dst bs ws0 n
        ∧ A = empAssertion) :=
  DCode.seq
    (DCode.seq
      (DCode.dwhile "copy" (.bne .x12 .x0) n
        (fun i rf ws A => mcInv src dst bs ws0 n i rf ws A
          ∧ mcStatic src dst bs ws0 n)
        (by
          rintro rf ws A ⟨h10, h11, h12, hws, hst, hA⟩
          exact ⟨⟨by simpa using h10, by simpa using h11, by simpa using h12,
            Nat.zero_le n, by simpa [hst.2.1] using hws, hA⟩, hst⟩)
        (fun i =>
          DCode.block "byte"
            [.LBU .x5 .x10 (0 : BitVec 12), .SB .x11 .x5 (0 : BitVec 12),
             .ADDI .x10 .x10 (1 : BitVec 12), .ADDI .x11 .x11 (1 : BitVec 12),
             .ADDI .x12 .x12 (-1 : BitVec 12)]
            (by decide)
            (fun _ rf ws A hlen hpre => by
              obtain ⟨_hi, ⟨⟨h10, h11, h12, hile, hws, hA⟩,
                ⟨hbs, hw, hn32, hsw, hdw, hdisj⟩⟩, hg⟩ := hpre
              have hwsn : ws.length = n := hlen
              have hin : i < n := by
                simp only [Cond.holds, RegFile.get_x0, ne_eq] at hg
                rw [h12] at hg
                rcases Nat.lt_or_ge i n with h | h
                · exact h
                · exact absurd (by omega : n - i = 0)
                    (fun he => hg (by rw [he]; rfl))
              have hno : ¬ inRw dst ws
                  (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
                rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
                  from by decide]
                unfold inRw
                rw [hwsn]
                intro hcontra
                rcases hdisj with h | h <;> bv_omega
              refine ⟨?_, ?_, trivial, trivial, trivial, trivial⟩
              · exact mc_vc _ _ _ _ 1 hno (by
                  rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
                    from by decide]
                  show 1 ∣ (src + BitVec.ofNat 64 i + 0 - src).toNat
                    ∧ (src + BitVec.ofNat 64 i + 0 - src).toNat + 1
                      ≤ bs.length
                  rw [show (src + BitVec.ofNat 64 i + 0 - src).toNat = i
                    from by bv_omega]
                  exact ⟨Nat.one_dvd i, by omega⟩)
              · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hno]
                refine ⟨?_, Nat.one_dvd _⟩
                rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
                  h11, show signExtend12 (0 : BitVec 12) = (0 : Word)
                    from by decide]
                unfold inRw
                rw [hwsn,
                  show (dst + BitVec.ofNat 64 i + 0 - dst).toNat = i from
                    by bv_omega]
                exact (by omega : i + 1 ≤ n))
            (by
              rintro rf ws A hlen ⟨_hi, ⟨⟨h10, h11, h12, hile, hws, hA⟩,
                ⟨hbs, hw, hn32, hsw, hdw, hdisj⟩⟩, hg⟩
              have hwsn : ws.length = n := hlen
              have hin : i < n := by
                simp only [Cond.holds, RegFile.get_x0, ne_eq] at hg
                rw [h12] at hg
                rcases Nat.lt_or_ge i n with h | h
                · exact h
                · exact absurd (by omega : n - i = 0)
                    (fun he => hg (by rw [he]; rfl))
              have hno : ¬ inRw dst ws
                  (rf.get .x10 + signExtend12 (0 : BitVec 12)) 1 := by
                rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
                  from by decide]
                unfold inRw
                rw [hwsn]
                intro hcontra
                rcases hdisj with h | h <;> bv_omega
              simp only [execBlock_cons, execBlock_nil,
                execInstrRF_lbu_ro _ _ _ _ _ _ _ hno, execInstrRF_sb',
                execInstrRF_addi']
              have hb : (Region.mk src bs).byteAt
                  (rf.get .x10 + signExtend12 (0 : BitVec 12))
                  = bs[i]'(by omega) := by
                unfold Region.byteAt
                rw [h10, show signExtend12 (0 : BitVec 12) = (0 : Word)
                  from by decide,
                  show (src + BitVec.ofNat 64 i + 0 - src).toNat = i from
                    by bv_omega]
                exact getD_eq_getElem' bs i (by omega)
              have hoff : ((rf.set .x5 (BitVec.zeroExtend 64
                    ((Region.mk src bs).byteAt
                      (rf.get .x10 + signExtend12 (0 : BitVec 12))))).get .x11
                  + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
                rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
                  h11, show signExtend12 (0 : BitVec 12) = (0 : Word)
                    from by decide]
                bv_omega
              refine ⟨⟨?_, ?_, ?_, by omega, ?_, hA⟩,
                ⟨hbs, hw, hn32, hsw, hdw, hdisj⟩⟩
              · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x12),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
                  RegFile.get_set_self _ _ _ (by decide),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
                  h10, show signExtend12 (1 : BitVec 12) = (1 : Word)
                    from by decide]
                bv_omega
              · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x12),
                  RegFile.get_set_self _ _ _ (by decide),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
                  h11, show signExtend12 (1 : BitVec 12) = (1 : Word)
                    from by decide]
                bv_omega
              · rw [RegFile.get_set_self _ _ _ (by decide),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
                  RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
                  h12, show signExtend12 (-1 : BitVec 12)
                    = BitVec.ofNat 64 (2 ^ 64 - 1) from by decide]
                bv_omega
              · rw [hoff, setBytes_singleton,
                  RegFile.get_set_self _ _ _ (by decide), hb,
                  truncate_zeroExtend_byte, hws]
                exact mc_copy_step bs ws0 n i hin hbs hw))
        (by
          rintro rf ws A ⟨⟨h10, h11, h12, hile, hws, hA⟩,
            ⟨hbs, hw, hn32, _⟩⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
          rw [h12]
          simp))
      (DCode.pure "wrap"
        (by
          rintro rf ws A ⟨⟨i, hile, ⟨h10, h11, h12, _hile, hws, hA⟩,
            ⟨hbs, hw, hn32, hsw, hdw, hdisj⟩⟩, hng⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hng
          rw [h12] at hng
          have hieq : i = n := by
            have : n - i = 0 := by bv_omega
            omega
          subst hieq
          rw [hws, show ws0.drop i = [] from
            List.drop_eq_nil_of_le (by omega), List.append_nil]
          exact ⟨rfl, ⟨hbs, hw, hn32, hsw, hdw, hdisj⟩, hA⟩)))
    (DCode.retJalr "mcr")

/-! ## The generated code and spec -/

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- The generated code. -/
def eddMemcpy_prog : Program :=
  (mcDeriv 0 0 [] [] 0).stmt.flatten 0

-- Pinned instruction sequence (build-time evaluation): byte-identical to
-- the previously hand-written routine.
#guard (eddMemcpy_prog : List Instr) ==
    [ .BEQ .x12 .x0 (28 : BitVec 13),
      .LBU .x5 .x10 (0 : BitVec 12),
      .SB .x11 .x5 (0 : BitVec 12),
      .ADDI .x10 .x10 (1 : BitVec 12),
      .ADDI .x11 .x11 (1 : BitVec 12),
      .ADDI .x12 .x12 (-1 : BitVec 12),
      .JAL .x0 (-24 : BitVec 21),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard eddMemcpy_prog.length = 8

/-- The code does not depend on the ghost arguments — the general
    statement (#12805): flattening the derivation at ANY ghosts, at any
    base, yields the same instructions as the pinned program's ghosts.
    The ghosts only enter `Prop`-valued annotations, which `flatten`
    drops, so this is definitional. -/
theorem mcDeriv_flatten_ghost_free (src dst : Word)
    (bs ws0 : List (BitVec 8)) (n : Nat) (base : Word) :
    (mcDeriv src dst bs ws0 n).stmt.flatten base
      = (mcDeriv 0 0 [] [] 0).stmt.flatten base := rfl

-- The sampled pin kept as a cheap build-time witness of the theorem above.
#guard (((mcDeriv 8 16 [0] [0] 1).stmt.flatten 0) : List Instr)
    == (eddMemcpy_prog : List Instr)

/-- The generated multi-exit spec: the `ra`-framed triple — the window
    ends as the `n`-byte source prefix. -/
theorem eddMemcpy_retSpec (src dst : Word) (bs ws0 : List (BitVec 8))
    (n : Nat) (base ret : Word)
    (hro : (Region.mk src bs).wf) (hrw : (RwRegion.mk dst n).wf)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (mcDeriv src dst bs ws0 n).stmt.steps base ret
      (CodeReq.ofProg base ((mcDeriv src dst bs ws0 n).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk src bs) (RwRegion.mk dst n)
          (fun rf ws A => rf.get .x10 = src ∧ rf.get .x11 = dst ∧
            rf.get .x12 = BitVec.ofNat 64 n ∧ ws = ws0 ∧
            mcStatic src dst bs ws0 n ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM (Region.mk src bs) (RwRegion.mk dst n)
          (fun _ ws A => ws = bs.take n ∧ mcStatic src dst bs ws0 n
            ∧ A = empAssertion)) :=
  DCode.retSpec (mcDeriv src dst bs ws0 n) base ret
    hro hrw halign (fun _ _ h => h)

end EddMemcpySAsm

end EvmAsm.Codegen
