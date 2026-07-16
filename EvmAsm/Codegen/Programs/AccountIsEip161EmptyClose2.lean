/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose2

  Closing composition for the whole-program K137 contract
  `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Builds on the three RLP call adapters + prologue + epilogue
  (`AccountIsEip161EmptyClose.lean`) and the three byte-scan loop lemmas
  (`AccountIsEip161EmptyLoop.lean`), composing the field-processing segments,
  the four-way verdict-store block, and the model tie into the top-level
  caller contract.

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-- Discharge a `.pcFree` side goal over frames of `bytesRegion`/`regIs`/`memIs`
    cells. -/
local macro "pcfR" : tactic =>
  `(tactic| repeat' first
    | exact bytesRegion_pcFree _ _
    | exact pcFree_regIs
    | exact pcFree_regOwn
    | exact pcFree_memIs
    | exact pcFree_memOwn
    | apply pcFree_sepConj
    | pcFree)

/-! ## RLP content-span bound

    From K20's abstract `Success`, the selected field's content window
    `[offset, offset+len)` fits inside the account buffer.  Derived from the
    caller's `hbound` "buffer-fits" precondition (the same honest precondition
    the header callers carry, e.g. `HeaderReceiptsRootSpec.hbound`), fed through
    the last-decode extraction `aieLastDecodeBound`
    (template: `HeaderReceiptsRootSpec.herrLastDecodeBound`). -/

/-- From the final decode of a strict `index`-th item (in a `listLen`-window
    list), extract the last item's raw decode at some offset `off ≤ listLen`. -/
private theorem aieLastDecodeBound {base : Word} {bytes : List (BitVec 8)}
    {endOff : Nat} (hover : base.toNat + endOff + 9 < 2 ^ 64) :
    ∀ {index startOff : Nat} {next len : Word},
      StrictNthItem bytes base (base + BitVec.ofNat 64 endOff)
        index startOff next len →
      startOff ≤ endOff →
      ∃ off, off ≤ endOff ∧ rlpItemDecode bytes off (base + BitVec.ofNat 64 off)
        (base + BitVec.ofNat 64 endOff) next len := by
  intro index startOff next len h
  induction h with
  | zero off n l hi => exact fun hst => ⟨off, hst, hi⟩
  | succ i off n l fn fl hi hrest ih =>
      intro hst
      exact ih (EvmAsm.Codegen.BalAccountNonstorageFinalsSpec.rlpItemDecode_advance
        hi hst hover).2.2

/-- **Content-span bound.**  Given the buffer-fits precondition `hbound`, a
    successful field selection has its content window inside the buffer:
    `offset.toNat + len.toNat ≤ bytes.length`. -/
theorem aieSpanBound (bytes : List (BitVec 8)) (accBase : Word) (listLen index : Nat)
    (offset len : Word)
    (hover : accBase.toNat + listLen + 9 < 2 ^ 64)
    (hbound : ∀ o next len', o ≤ listLen →
      rlpItemDecode bytes o (accBase + BitVec.ofNat 64 o)
        (accBase + BitVec.ofNat 64 listLen) next len' →
      (next - len' - accBase).toNat + len'.toNat ≤ bytes.length)
    (hsucc : Success bytes accBase listLen index offset len) :
    offset.toNat + len.toNat ≤ bytes.length := by
  obtain ⟨cursorOff, endPtr, next, hpay, hnth, hoff⟩ := hsucc
  have hend := hpay.end_eq
  subst hend
  have hcle := hpay.cursor_le
  obtain ⟨off, hoffle, hdec⟩ := aieLastDecodeBound hover hnth hcle
  rw [hoff]
  exact hbound off next len hoffle hdec

#print axioms aieSpanBound

/-! ## Code-membership macro into the full closure -/

/-- `k`-th instruction membership into the full closure `fullCode`. -/
local macro "aieFC" k:term ", " A:term ", " ins:term : term =>
  `((fun a i hi => aie_mono a i
      (CodeReq.ofProg_mem_at AB $A accountIsEip161Empty_prog $k $ins (by bv_omega)
        (by rw [aie_prog_length]; omega) rfl (by rw [aie_prog_length]; norm_num) a i hi)))

/-! ## Verdict-store tails ([87]-[101], all converging at the epilogue AB+408)

    Four fall-in targets, each writing `x10` (the ABI status `a0`) and possibly
    the output cell, then jumping to the shared epilogue entry `AB+408`:
      * `AB+348` empty      → out := 1, a0 := 0   ([87]-[95], 5 NOPs + store)
      * `AB+384` not-empty  → out := 0, a0 := 0   ([96]-[98])
      * `AB+396` fail       → a0 := 1             ([99]-[100])
      * `AB+404` sizefail   → a0 := 2             ([101], falls through)  -/

set_option maxRecDepth 8000 in
/-- Not-empty verdict tail ([96]-[98], `AB+384 → AB+408`): store `0` to the
    output cell and set `a0 = 0`. -/
theorem aieVerdictNotEmpty (outPtr v10 oldout : Word) :
    cpsTripleWithin 3 (AB + 384) (AB + 408) fullCode
      ((.x18 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
      ((.x18 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (0 : Word))) := by
  -- [96] SD x18 x0 0 : out := 0
  have h96 := sd_spec_gen_within .x18 .x0 outPtr (0 : Word) oldout (0 : BitVec 12) (AB + 384)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h96
  have e96 := cpsTripleWithin_extend_code (aieFC 96, (AB + 384), (.SD .x18 .x0 (0 : BitVec 12))) h96
  have f96 := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10)) (by pcfR) e96
  -- [97] LI x10 0
  have h97 := li_spec_gen_within .x10 v10 (0 : Word) (AB + 388) (by decide)
  have e97 := cpsTripleWithin_extend_code (aieFC 97, (AB + 388), (.LI .x10 (0 : Word))) h97
  have f97 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (outPtr ↦ₘ (0 : Word))) (by pcfR) e97
  -- [98] JAL x0 16 → AB+408
  have h98 := jal_x0_spec_gen_within (16 : BitVec 21) (AB + 392)
  rw [show (AB + 392 : Word) + signExtend21 (16 : BitVec 21) = AB + 408 from by
    rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]; bv_omega] at h98
  have e98 := cpsTripleWithin_extend_code (aieFC 98, (AB + 392), (.JAL .x0 (16 : BitVec 21))) h98
  have f98 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ (0 : Word))) (by pcfR) e98
  rw [sepConj_emp_left'] at f98
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) f96 f97
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 f98
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s2)

#print axioms aieVerdictNotEmpty

set_option maxRecDepth 8000 in
/-- Parse-fail verdict tail ([99]-[100], `AB+396 → AB+408`): set `a0 = 1`. -/
theorem aieVerdictFail (v10 : Word) :
    cpsTripleWithin 2 (AB + 396) (AB + 408) fullCode
      ((.x10 ↦ᵣ v10))
      ((.x10 ↦ᵣ (1 : Word))) := by
  -- [99] LI x10 1
  have h99 := li_spec_gen_within .x10 v10 (1 : Word) (AB + 396) (by decide)
  have e99 := cpsTripleWithin_extend_code (aieFC 99, (AB + 396), (.LI .x10 (1 : Word))) h99
  -- [100] JAL x0 8 → AB+408
  have h100 := jal_x0_spec_gen_within (8 : BitVec 21) (AB + 400)
  rw [show (AB + 400 : Word) + signExtend21 (8 : BitVec 21) = AB + 408 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]; bv_omega] at h100
  have e100 := cpsTripleWithin_extend_code (aieFC 100, (AB + 400), (.JAL .x0 (8 : BitVec 21))) h100
  have f100 := cpsTripleWithin_frameR ((.x10 ↦ᵣ (1 : Word))) (by pcfR) e100
  rw [sepConj_emp_left'] at f100
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) e99 f100
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s1)

#print axioms aieVerdictFail

set_option maxRecDepth 8000 in
/-- Size-fail verdict tail ([101], `AB+404 → AB+408`): set `a0 = 2`, fall through
    to the epilogue. -/
theorem aieVerdictSizeFail (v10 : Word) :
    cpsTripleWithin 1 (AB + 404) (AB + 408) fullCode
      ((.x10 ↦ᵣ v10))
      ((.x10 ↦ᵣ (2 : Word))) := by
  -- [101] LI x10 2
  have h101 := li_spec_gen_within .x10 v10 (2 : Word) (AB + 404) (by decide)
  rw [show (AB + 404 : Word) + 4 = AB + 408 from by bv_omega] at h101
  exact cpsTripleWithin_extend_code (aieFC 101, (AB + 404), (.LI .x10 (2 : Word))) h101

#print axioms aieVerdictSizeFail

set_option maxRecDepth 8000 in
/-- Empty verdict tail ([87]-[95], `AB+348 → AB+408`): 5 NOPs, then store `1`
    to the output cell and set `a0 = 0`. -/
theorem aieVerdictEmpty (outPtr v5 v10 oldout : Word) :
    cpsTripleWithin 9 (AB + 348) (AB + 408) fullCode
      ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
      ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
        (outPtr ↦ₘ (1 : Word))) := by
  -- [87]-[91] NOP × 5
  have hn87 := nop_spec_within (AB + 348)
  have en87 := cpsTripleWithin_extend_code (aieFC 87, (AB + 348), (.NOP)) hn87
  have hn88 := nop_spec_within (AB + 352)
  have en88 := cpsTripleWithin_extend_code (aieFC 88, (AB + 352), (.NOP)) hn88
  have hn89 := nop_spec_within (AB + 356)
  have en89 := cpsTripleWithin_extend_code (aieFC 89, (AB + 356), (.NOP)) hn89
  have hn90 := nop_spec_within (AB + 360)
  have en90 := cpsTripleWithin_extend_code (aieFC 90, (AB + 360), (.NOP)) hn90
  have hn91 := nop_spec_within (AB + 364)
  have en91 := cpsTripleWithin_extend_code (aieFC 91, (AB + 364), (.NOP)) hn91
  -- [92] LI x5 1
  have h92 := li_spec_gen_within .x5 v5 (1 : Word) (AB + 368) (by decide)
  have e92 := cpsTripleWithin_extend_code (aieFC 92, (AB + 368), (.LI .x5 (1 : Word))) h92
  have f92 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout)) (by pcfR) e92
  -- [93] SD x18 x5 0 : out := 1
  have h93 := sd_spec_gen_within .x18 .x5 outPtr (1 : Word) oldout (0 : BitVec 12) (AB + 372)
  rw [show outPtr + signExtend12 (0 : BitVec 12) = outPtr from by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]; bv_omega] at h93
  have e93 := cpsTripleWithin_extend_code (aieFC 93, (AB + 372), (.SD .x18 .x5 (0 : BitVec 12))) h93
  have f93 := cpsTripleWithin_frameR ((.x10 ↦ᵣ v10)) (by pcfR) e93
  -- [94] LI x10 0
  have h94 := li_spec_gen_within .x10 v10 (0 : Word) (AB + 376) (by decide)
  have e94 := cpsTripleWithin_extend_code (aieFC 94, (AB + 376), (.LI .x10 (0 : Word))) h94
  have f94 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (outPtr ↦ₘ (1 : Word))) (by pcfR) e94
  -- [95] JAL x0 28 → AB+408
  have h95 := jal_x0_spec_gen_within (28 : BitVec 21) (AB + 380)
  rw [show (AB + 380 : Word) + signExtend21 (28 : BitVec 21) = AB + 408 from by
    rw [show signExtend21 (28 : BitVec 21) = (28 : Word) from by decide]; bv_omega] at h95
  have e95 := cpsTripleWithin_extend_code (aieFC 95, (AB + 380), (.JAL .x0 (28 : BitVec 21))) h95
  have f95 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ (1 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
      (outPtr ↦ₘ (1 : Word))) (by pcfR) e95
  rw [sepConj_emp_left'] at f95
  -- The five NOPs carry the whole payload as a frame.
  have payload : Assertion :=
    (.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout)
  have fn87 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
    (by pcfR) en87
  have fn88 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
    (by pcfR) en88
  have fn89 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
    (by pcfR) en89
  have fn90 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
    (by pcfR) en90
  have fn91 := cpsTripleWithin_frameR
    ((.x18 ↦ᵣ outPtr) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (outPtr ↦ₘ oldout))
    (by pcfR) en91
  rw [sepConj_emp_left'] at fn87 fn88 fn89 fn90 fn91
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) fn87 fn88
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s1 fn89
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s2 fn90
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s3 fn91
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s4 f92
  have s6 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s5 f93
  have s7 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s6 f94
  have s8 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_chunked hp) s7 f95
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
      (fun _ hq => by xperm_chunked hq) s8)

#print axioms aieVerdictEmpty

end EvmAsm.Codegen.AccountIsEip161EmptySpec
