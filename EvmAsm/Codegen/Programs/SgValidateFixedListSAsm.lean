/-
  EvmAsm.Codegen.Programs.SgValidateFixedListSAsm

  Proof-first (DCode) port of `sg_validate_fixed_list` — the SSZ
  fixed-list framing validator on the stateless-guest input-decode path
  (`a1` = section byte length, `a2` = element size, `a3` = max element
  count; returns `a0 = 0` iff `a2 ≠ 0 ∧ a1 % a2 = 0 ∧ a1 / a2 ≤ a3`).

  First user of the guard-cascade derivation step (`dretCascade` /
  `Stmt.retCascade`): three guards share ONE bad tail (`li a0,1; ret`),
  the machine idiom a tree of `retIf`s cannot express without duplicating
  the tail.  Consumed through `DCode.retSpec` (the `Stmt.retSound`
  multi-exit path).  Byte-identity with the previously hand-written
  routine in `StatelessGuestEpilogue.lean` verified by assemble+cmp; the
  emitted bundle slice is now `emitProgram` of the generated program.
-/

import EvmAsm.Rv64.SAsm.Deriv

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

namespace SgValidateFixedListSAsm

/-- Register-only routine. -/
local infix:36 " ⤳ " => DCode Region.empty RwRegion.empty

/-! ## The routine's semantics -/

/-- The SSZ fixed-list framing condition: a nonzero element size that
    tiles the section exactly, within the element-count limit. -/
def sgvOk (len esz maxc : Word) : Prop :=
  esz ≠ 0 ∧ len % esz = 0 ∧ ¬ (BitVec.ult maxc (len / esz) = true)

instance (len esz maxc : Word) : Decidable (sgvOk len esz maxc) := by
  unfold sgvOk
  infer_instance

/-- The returned status flag. -/
def sgvOut (len esz maxc : Word) : Word :=
  if sgvOk len esz maxc then 0 else 1

/-! ## The stages -/

/-- Stage list: `beqz a2 → bad`; `remu; bnez t0 → bad`;
    `divu; bgtu t0, a3 → bad` (encoded as `bltu a3, t0`). -/
def sgvStages : List (List Instr × Cond) :=
  [ ([], .beq .x12 .x0),
    ([.REMU .x5 .x11 .x12], .bne .x5 .x0),
    ([.DIVU .x5 .x11 .x12], .bltu .x13 .x5) ]

/-- Cascade invariant: after stage `k`, the first `k` checks passed. -/
def sgvInv (len esz maxc : Word) : Nat → Reach
  | 0 => fun rf _ A => rf.get .x11 = len ∧ rf.get .x12 = esz ∧
      rf.get .x13 = maxc ∧ A = empAssertion
  | 1 => fun rf _ A => rf.get .x11 = len ∧ rf.get .x12 = esz ∧
      rf.get .x13 = maxc ∧ esz ≠ 0 ∧ A = empAssertion
  | 2 => fun rf _ A => rf.get .x11 = len ∧ rf.get .x12 = esz ∧
      rf.get .x13 = maxc ∧ esz ≠ 0 ∧ len % esz = 0 ∧ A = empAssertion
  | _ => fun _ _ A => sgvOk len esz maxc ∧ A = empAssertion

/-- Bad-entry states: some check failed. -/
def sgvBad (len esz maxc : Word) : Reach :=
  fun _ _ A => ¬ sgvOk len esz maxc ∧ A = empAssertion

/-! ## The derivation -/

/-- Proof-first SSZ fixed-list validation: a three-guard cascade into one
    shared failure tail; each success tail sets the status and returns. -/
def sgvDeriv (len esz maxc : Word) :
    (fun rf _ A => rf.get .x11 = len ∧ rf.get .x12 = esz ∧
      rf.get .x13 = maxc ∧ A = empAssertion)
      ⤳ (fun rf _ A => rf.get .x10 = sgvOut len esz maxc
          ∧ A = empAssertion) :=
  DCode.dretCascade "checks" sgvStages
    (sgvInv len esz maxc) (sgvBad len esz maxc)
    (fun _ _ _ h => h)
    ⟨⟨rfl,
      fun h => absurd h (by decide),
      (by
        rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨h11, h12, h13, hA⟩, rfl, rfl⟩ hnc
        simp only [Cond.holds, RegFile.get_x0] at hnc ⊢
        exact ⟨h11, h12, h13, by rw [h12] at hnc; exact hnc, hA⟩),
      (by
        rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨h11, h12, h13, hA⟩, rfl, rfl⟩ hc
        simp only [Cond.holds, RegFile.get_x0] at hc
        rw [h12] at hc
        exact ⟨fun hok => hok.1 hc, hA⟩)⟩,
     ⟨rfl,
      fun h => absurd h (by decide),
      (by
        rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨h11, h12, h13, hesz, hA⟩, rfl, rfl⟩
          hnc
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hnc ⊢
        simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hnc
        rw [RegFile.get_set_self _ _ _ (by decide), h11, h12] at hnc
        have hrem : len % esz = 0 := by
          rw [rv64_remu, if_neg (by simpa using hesz)] at hnc
          exact hnc
        refine ⟨?_, ?_, ?_, hesz, hrem, hA⟩
        · rw [RegFile.get_set_ne _ _ _ _ (by decide), h11]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide), h12]
        · rw [RegFile.get_set_ne _ _ _ _ (by decide), h13])
      ,
      (by
        rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨h11, h12, h13, hesz, hA⟩, rfl, rfl⟩
          hc
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hc
        simp only [Cond.holds, RegFile.get_x0, ne_eq] at hc
        rw [RegFile.get_set_self _ _ _ (by decide), h11, h12,
          rv64_remu, if_neg (by simpa using hesz)] at hc
        exact ⟨fun hok => hc hok.2.1, hA⟩)⟩,
     ⟨rfl,
      fun h => absurd h (by decide),
      (by
        rintro rf ws A ⟨rf₀, ws₀, hlen,
          ⟨h11, h12, h13, hesz, hrem, hA⟩, rfl, rfl⟩ hnc
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hnc ⊢
        simp only [Cond.holds] at hnc
        rw [RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide), h11, h12, h13,
          rv64_divu, if_neg (by simpa using hesz)] at hnc
        exact ⟨⟨hesz, hrem, hnc⟩, hA⟩)
      ,
      (by
        rintro rf ws A ⟨rf₀, ws₀, hlen,
          ⟨h11, h12, h13, hesz, hrem, hA⟩, rfl, rfl⟩ hc
        simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          at hc
        simp only [Cond.holds] at hc
        rw [RegFile.get_set_self _ _ _ (by decide),
          RegFile.get_set_ne _ _ _ _ (by decide), h11, h12, h13,
          rv64_divu, if_neg (by simpa using hesz)] at hc
        exact ⟨fun hok => hok.2.2 hc, hA⟩)⟩,
     trivial⟩
    (DCode.seq
      (DCode.block "ok0" [.LI .x10 (0 : Word)] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨hok, hA⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          refine ⟨?_, hA⟩
          rw [RegFile.get_set_self _ _ _ (by decide), sgvOut, if_pos hok]))
      (DCode.retJalr "okr"))
    (DCode.seq
      (DCode.block "bad1" [.LI .x10 (1 : Word)] (by decide)
        (fun h => absurd h (by decide))
        (by
          rintro rf ws A _ ⟨hbad, hA⟩
          simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
          refine ⟨?_, hA⟩
          rw [RegFile.get_set_self _ _ _ (by decide), sgvOut, if_neg hbad]))
      (DCode.retJalr "badr"))

/-! ## The generated code and spec -/

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- The generated code (the return tails are IN the code — no epilogue). -/
def sgValidateFixedList_prog : Program :=
  (sgvDeriv 0 0 0).stmt.flatten 0

-- Pinned instruction sequence (build-time evaluation): byte-identical to
-- the previously hand-written routine.
#guard (sgValidateFixedList_prog : List Instr) ==
    [ .BEQ .x12 .x0 (28 : BitVec 13),
      .REMU .x5 .x11 .x12,
      .BNE .x5 .x0 (20 : BitVec 13),
      .DIVU .x5 .x11 .x12,
      .BLTU .x13 .x5 (12 : BitVec 13),
      .LI .x10 (0 : Word),
      .JALR .x0 .x1 (0 : BitVec 12),
      .LI .x10 (1 : Word),
      .JALR .x0 .x1 (0 : BitVec 12) ]

#guard sgValidateFixedList_prog.length = 9

-- The code does not depend on the ghost arguments (sampled).
#guard (((sgvDeriv 3 5 7).stmt.flatten 0) : List Instr)
    == (sgValidateFixedList_prog : List Instr)

/-- The generated multi-exit spec: the `ra`-framed triple at any base and
    aligned return address — `a0` ends as the framing-validity flag. -/
theorem sgValidateFixedList_retSpec (len esz maxc base ret : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (sgvDeriv len esz maxc).stmt.steps base ret
      (CodeReq.ofProg base ((sgvDeriv len esz maxc).stmt.flatten base))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty RwRegion.empty
          (fun rf _ A => rf.get .x11 = len ∧ rf.get .x12 = esz ∧
            rf.get .x13 = maxc ∧ A = empAssertion))
      (((.x1 : Reg) ↦ᵣ ret)
        ** asrtM Region.empty RwRegion.empty
          (fun rf _ A => rf.get .x10 = sgvOut len esz maxc
            ∧ A = empAssertion)) :=
  DCode.retSpec (sgvDeriv len esz maxc) base ret
    Region.empty_wf RwRegion.empty_wf halign (fun _ _ h => h)

end SgValidateFixedListSAsm

end EvmAsm.Codegen
