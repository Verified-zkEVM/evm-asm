/-
  EvmAsm.Codegen.Programs.Bn254Fq12ZeroSAsm

  Verified SAsm port of `bnq_zero`: zero the 384-byte BN254 FQ12 buffer at `a0`.  The emitted routine is a bottom-test dword loop:
  initialize `x5 = 12`, store a zero dword, advance `a0`, decrement `x5`, and
  branch back while `x5 != 0`.

  The postcondition is the genuine buffer effect: all 384 bytes are zero.  The
  structured `doWhile` body is byte-identical to `bnqZero_prog` including
  the trailing `ret` drift guard below.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Bn254Fq12
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Bn254Fq12ZeroSAsm

def zeroWin384 (orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  List.replicate (8 * i) (0 : BitVec 8) ++ orig.drop (8 * i)

theorem zeroWin384_zero (orig : List (BitVec 8)) : zeroWin384 orig 0 = orig := by
  simp [zeroWin384]

theorem zeroWin384_48_eq (orig : List (BitVec 8)) (h : orig.length = 384) :
    zeroWin384 orig 48 = List.replicate 384 (0 : BitVec 8) := by
  simp only [zeroWin384, Nat.reduceMul,
    List.drop_eq_nil_of_le (by omega : orig.length <= 384), List.append_nil]

theorem length_zeroWin384 (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 384) (hi : i <= 48) : (zeroWin384 orig i).length = 384 := by
  simp only [zeroWin384, List.length_append, List.length_replicate, List.length_drop, h]
  omega

theorem zeroWin384_step (orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 384) (hi : i < 48) :
    setBytes (zeroWin384 orig i) (8 * i) (dwordBytes (0 : Word)) = zeroWin384 orig (i + 1) := by
  rw [zeroWin384]
  rw [setBytes_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hsuf : (orig.drop (8 * i)).length = 384 - 8 * i := by simp [h]
  have hfit : 0 + (dwordBytes (0 : Word)).length <= (orig.drop (8 * i)).length := by
    rw [length_dwordBytes, hsuf]
    omega
  have hslot := setBytes_slot (orig.drop (8 * i)) (dwordBytes (0 : Word)) 0 hfit
  rw [List.drop_zero, length_dwordBytes] at hslot
  have hdrop : (setBytes (orig.drop (8 * i)) 0 (dwordBytes (0 : Word))).drop 8
      = (orig.drop (8 * i)).drop 8 := by
    simpa [length_dwordBytes] using
      (setBytes_drop_of_le (dwordBytes (0 : Word)) (orig.drop (8 * i)) 0 8 (by
        rw [length_dwordBytes]))
  have hset : setBytes (List.drop (8 * i) orig) 0 (dwordBytes (0 : Word))
      = dwordBytes (0 : Word) ++ (List.drop (8 * i) orig).drop 8 := by
    conv_lhs =>
      rw [<- List.take_append_drop 8 (setBytes (List.drop (8 * i) orig) 0 (dwordBytes 0))]
    rw [hslot, hdrop]
  rw [hset]
  rw [show (List.drop (8 * i) orig).drop 8 = orig.drop (8 * (i + 1)) from by
    rw [List.drop_drop]
    congr 1]
  rw [show dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) from by decide]
  simp only [zeroWin384]
  rw [<- List.append_assoc]
  congr 1
  rw [List.replicate_append_replicate]
  congr

def zeroStepBlock : List Instr :=
  [.SD .x10 .x0 (0 : BitVec 12),
   .ADDI .x10 .x10 (8 : BitVec 12),
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def zeroStepRf (rf : RegFile) : RegFile :=
  let r1 := rf.set .x10 (rf.get .x10 + signExtend12 (8 : BitVec 12))
  r1.set .x7 (r1.get .x7 + signExtend12 (-1 : BitVec 12))

theorem zeroStepRf_get_x10 (rf : RegFile) :
    (zeroStepRf rf).get .x10 = rf.get .x10 + signExtend12 (8 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zeroStepRf_get_x7 (rf : RegFile) :
    (zeroStepRf rf).get .x7 =
      rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold zeroStepRf
  simp only [RegFile.get_set_self, RegFile.get_set_ne, ne_eq, reduceCtorEq,
    not_false_eq_true]

theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hi : i < 48)
    (hx10 : rf.get .x10 = dst + BitVec.ofNat 64 (8 * i)) :
    execBlock reg dst rf ws zeroStepBlock
      = (zeroStepRf rf, setBytes ws (8 * i) (dwordBytes (0 : Word))) := by
  have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  apply Prod.ext
  . rfl
  . show setBytes ws ((rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat)
        (dwordBytes (rf.get .x0)) = setBytes ws (8 * i) (dwordBytes (0 : Word))
    rw [haddr, RegFile.get_x0]

def zeroInv (dst : Word) (orig : List (BitVec 8)) :
    Nat -> RegFile -> List (BitVec 8) -> Assertion -> Prop :=
  fun i rf ws A =>
    rf.get .x10 = dst + BitVec.ofNat 64 (8 * (i + 1)) ∧
    rf.get .x7 = BitVec.ofNat 64 (48 - (i + 1)) ∧
    i < 48 ∧ orig.length = 384 ∧ ws = zeroWin384 orig (i + 1) ∧
    A = empAssertion

def bnqZeroBody (dst : Word) (orig : List (BitVec 8)) : Stmt :=
  .block "init" [.LI .x7 (48 : Word)] ;;;
  .doWhile "loop" (.bne .x7 .x0) 47 (zeroInv dst orig)
    (.block "zero" zeroStepBlock)

def bnqZeroFn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "bnqZero"
  rw := ⟨dst, 384⟩
  pre := fun rf ws A =>
    rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 384 ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = dst + BitVec.ofNat 64 384 ∧ rf.get .x7 = 0 ∧
    ws = List.replicate 384 (0 : BitVec 8) ∧ A = empAssertion
  body := bnqZeroBody dst orig

def bnqZero_verified : Program :=
  (bnqZeroBody 0 []).flatten 0

#guard (bnqZero_verified : List Instr).length = 5
#guard (bnqZeroBody 0 []).flatten 0 = (bnqZeroBody 0 []).flatten 0x80000000
#guard (bnqZeroBody 0 []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = bnqZero_prog

theorem bnqZeroFn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 384⟩) (base : Word) :
    (bnqZeroFn dst orig).Spec base := by
  have hbase : (bnqZeroFn dst orig).rw.base = dst := rfl
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case bnqZero.loop.inv_init =>
    rintro rf' ws' A' h
    rcases h with ⟨rf0, ws0, -, hreach, rfl, rfl⟩
    rcases hreach with ⟨rfInit, wsInit, -, hpre, rfl, rfl⟩
    rcases hpre with ⟨hx10, rfl, hlen, hA⟩
    simp only [hbase]
    have hx10Init : (execBlock (bnqZeroFn dst ws0).region dst rfInit ws0
        [Instr.LI Reg.x7 48]).1.get .x10 = dst := by
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem, RegFile.get_set_ne,
        ne_eq, reduceCtorEq, not_false_eq_true, hx10]
    rw [zero_engine _ dst _ ws0 0 (by omega) (by simpa using hx10Init)]
    refine ⟨?_, ?_, by omega, hlen, ?_, hA⟩
    · rw [zeroStepRf_get_x10, hx10Init, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      bv_omega
    · rw [zeroStepRf_get_x7]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      decide
    · change setBytes ws0 (8 * 0) (dwordBytes (0 : Word)) = zeroWin384 ws0 (0 + 1)
      simpa [zeroWin384_zero ws0] using zeroWin384_step ws0 0 hlen (by omega)
  case bnqZero.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -, ⟨⟨hx10, hx5, hlt, hlen, hws₀, hA⟩, hcond⟩, rfl, rfl⟩
    simp only [hbase]
    rw [zero_engine _ dst rf₀ ws₀ (i + 1) (by omega) hx10]
    refine ⟨?_, ?_, by omega, hlen, ?_, hA⟩
    · rw [zeroStepRf_get_x10, hx10, show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from by decide]
      omega
    · rw [zeroStepRf_get_x7, hx5, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      interval_cases i <;> decide
    · rw [hws₀, zeroWin384_step orig (i + 1) hlen (by omega)]
  case bnqZero.loop.exhausted =>
    rintro rf ws A ⟨-, hx5, -, -, -, -⟩
    simp only [Cond.holds, hx5, not_not, RegFile.get_x0]
    decide
  case bnqZero.loop.body.zero.mem =>
    rintro rf ws A hlen (hpre | hloop)
    · rcases hpre with ⟨rfInit, wsInit, -, ⟨hx10, rfl, horiglen, -⟩, rfl, rfl⟩
      have hlen384 : ws.length = 384 := by
        change ws.length = 384 at hlen
        exact hlen
      have haddr0 : (dst + signExtend12 (0 : BitVec 12) - dst).toNat = 0 := by
        rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      simp only [zeroStepBlock, blockVCs, execInstrRF, aluSem, loadSem, storeSem,
        inRw, hbase, execBlock_cons, execBlock_nil, RegFile.get_set_ne, ne_eq,
        reduceCtorEq, not_false_eq_true, hx10, hlen384, haddr0, and_true]
      constructor
      · omega
      · exact Nat.dvd_zero 8
    · rcases hloop with ⟨i, hi, ⟨hx10, hx5, hlt, horiglen, hws, -⟩, hcond⟩
      have haddr : (rf.get .x10 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * (i + 1) := by
        rw [hx10, show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
        bv_omega
      have hlen384 : ws.length = 384 := by
        change ws.length = 384 at hlen
        exact hlen
      simp only [zeroStepBlock, blockVCs, loadSem, storeSem, inRw, hbase, haddr, hlen384,
        and_true]
      constructor
      · omega
      · exact Nat.dvd_mul_right 8 (i + 1)
  case bnqZero.post =>
    rintro rf ws A ⟨⟨i, hle, hx10, hx5, hlt, hlen, hws, hA⟩, hncond⟩
    have hi47 : i = 47 := by
      simp only [Cond.holds, hx5, RegFile.get_x0, not_not] at hncond
      interval_cases i <;> try contradiction
      rfl
    subst hi47
    refine ⟨?_, ?_, ?_, hA⟩
    · rw [hx10]
    · rw [hx5]
      decide
    · rw [hws, zeroWin384_48_eq orig hlen]


/-! ## Flat linked-entry contract (#12244)

    The own-`CodeReq` whole-routine triple. It lived only inside
    `Bn254Fq12SetOneSAsm.bnqZeroFlat_spec` before, as an unnamed intermediate that
    was immediately widened to that file's adjacency `CodeReq` — so the rowable
    statement existed but could not be cited. Naming it here, in the ROUTINE'S OWN
    module, is deliberate: the registry-coverage allowlist's own warning is that a
    flat sibling hiding in a caller's file is what makes these hard to find. -/

def bnqZeroCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bnq_zero : Word) bnqZero_prog

/-- The exposed registers other than `a0`; the callee owns the whole exposed file,
    which is what its `Fn.Spec` claims. -/
def bnqZeroScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Split the full exposed file into the `a0` atom plus the scratch atoms. -/
private theorem exposedRegs_split_zero (vf : Reg → Word) :
    regAtomsOf vf exposedRegs
      = ((.x10 ↦ᵣ vf .x10) ** regAtomsOf vf bnqZeroScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bnqZeroScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem x10_notin_zero_scratch : (.x10 : Reg) ∉ bnqZeroScratch := by decide

/-- **`bnq_zero`, whole-routine flat triple at the guest entry.**

    Zeroes the 48-dword (384-byte) buffer at `a0`, leaving `a0` advanced past it
    and `ra` intact. Derived from the structured `bnqZeroFn_spec` by
    `Fn.retSpecFlat` — no hand-written loop proof.

    Anchored over `bnqZeroCr = CodeReq.ofProg (GuestAddrs.bnq_zero) bnqZero_prog`,
    exactly the pairing in `GuestImageEntries.lean`, so this IS the image claim and
    is rowable. The post is COMPLETE and deterministic — all 48 dwords are
    `List.replicate 48 0`, the whole window, not an existential and not a prefix.

    Domain: ABI only (`RwRegion.wf ⟨dst, 384⟩`, `vs.length = 48`, aligned `ra`), so
    unlike the two-window converters this triple IS total over its argument type —
    `rw` is the only live window, hence no disjointness side condition.

    ⚠️ NOT to be confused with `Bn254Fq12SetOneSAsm.bnqZeroFlat_spec`, which agrees
    on entry, exit, pre and post but is anchored over the ADJACENCY `CodeReq`
    `CodeReq.ofProg (GuestAddrs.bnq_zero) (bnqZero_prog ++ bnqSetOne_prog)` — a
    claim about TWO routines being contiguous, strictly stronger than the
    single-program image pairing, and therefore not the image claim. It is now a
    one-line corollary of this theorem. -/
theorem bnqZeroFlatEntry_spec (ret dst : Word) (vs : List Word)
    (hlen : vs.length = 48)
    (hwf : RwRegion.wf ⟨dst, 384⟩)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (1 + 48 * (3 + 1) + 1) (GuestAddrs.bnq_zero : Word) ret bnqZeroCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** regOwns bnqZeroScratch
        ** dwordsIs dst vs)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ (dst + BitVec.ofNat 64 384))
        ** regOwns bnqZeroScratch
        ** dwordsIs dst (List.replicate 48 (0 : Word))) := by
  rw [show (1 + 48 * (3 + 1) + 1 : Nat)
      = (bnqZeroFn dst (vs.flatMap dwordBytes)).body.steps + 1 from rfl]
  -- Surface the scratch registers at concrete (peeled) valuations.
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bnqZeroScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** dwordsIs dst vs)
      (fun vf => ?_))
  -- The adapter, at the packed register file.
  have hlenB : (vs.flatMap dwordBytes).length = 384 := by
    rw [length_flatMap_dwordBytes, hlen]
  have had := Fn.retSpecFlat (bnqZeroFn dst (vs.flatMap dwordBytes))
    (GuestAddrs.bnq_zero : Word)
    (bnqZeroFn_spec dst (vs.flatMap dwordBytes) hwf
      (GuestAddrs.bnq_zero : Word))
    (by show 4 * (5 + 1) ≤ 2 ^ 64; decide) ret halign
    (fun r => if r = .x10 then dst else vf r)
    (vs.flatMap dwordBytes)
    hlenB
    (by
      refine ⟨?_, rfl, hlenB, rfl⟩
      show RegFile.get (fun r => if r = .x10 then dst else vf r) .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl)
    (fun _ _ _ h => h.2.2.2)
    (Q := (.x10 ↦ᵣ (dst + BitVec.ofNat 64 384)) ** regOwns bnqZeroScratch
      ** dwordsIs dst (List.replicate 48 (0 : Word)))
    (fun rf' ws' hlen' hpost' hp hh => by
      obtain ⟨hx10', hx7', hws', -⟩ := hpost'
      subst hws'
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_zero,
        show List.replicate 384 (0 : BitVec 8)
          = (List.replicate 48 (0 : Word)).flatMap dwordBytes from by
            rw [replicate_zero_flatMap_dwordBytes],
        ← dwordsIs_eq_bytesRegion,
        show rf' .x10 = dst + BitVec.ofNat 64 384 from by
          rw [show rf' .x10 = rf'.get .x10 from by
            rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]]
          exact hx10'] at hh
      have hh2 := sepConj_mono_left
        (sepConj_mono_right (regAtomsOf_to_regOwns (fun r => rf' r) bnqZeroScratch))
        hp hh
      xperm_hyp hh2)
  -- ⛔ NO `liftCode` below. Stopping here IS the change: the adapter's `CodeReq`
  -- is already `bnq_zero`'s own program, and widening it to the adjacency `bnqCr`
  -- is what made the only existing copy unrowable.
  rw [show (bnqZeroFn dst (vs.flatMap dwordBytes)).programRet (GuestAddrs.bnq_zero : Word)
      = bnqZero_prog from rfl] at had
  -- Reshape: strip the empty read-only region, unpack the register file.
  rw [show (bnqZeroFn dst (vs.flatMap dwordBytes)).region = Region.empty from rfl]
    at had
  rw [show bytesRegion Region.empty.base Region.empty.bytes = empAssertion from
    bytesRegion_nil _] at had
  rw [sepConj_emp_right', sepConj_emp_right'] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_zero,
    show (if (Reg.x10 : Reg) = .x10 then dst else vf .x10) = dst from if_pos rfl,
    regAtomsOf_congr (fun r => if r = .x10 then dst else vf r) vf bnqZeroScratch
      (fun r hr => by
        show (if r = .x10 then dst else vf r) = vf r
        exact if_neg (fun (hc : r = .x10) => x10_notin_zero_scratch (hc ▸ hr))),
    show (bnqZeroFn dst (vs.flatMap dwordBytes)).rw.base = dst from rfl,
    ← dwordsIs_eq_bytesRegion] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

end Bn254Fq12ZeroSAsm

end EvmAsm.Codegen
