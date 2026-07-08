/-
  EvmAsm.Rv64.SAsm.FramePort

  **Port-automation for sp-frame routines** (bead evm-asm-4ch8f.76 follow-up):
  collapses the mechanical boilerplate of an ABI-frame port — the
  `abiFrame_spec`/`abiFrameCall_spec`/`countdownLoop_spec` side-conditions,
  `pcFree` obligations, code-membership plumbing, and address bridges — into
  tactics, so each port reduces to its genuine core (body semantics + loop
  invariant + the disjunctive post).

  Standalone step-by-step guide (triage tiers, worked examples, checklist):
  **docs/porting-sp-frame-routines.md**.

  ## The recipe: how to port an sp-frame routine

  1. **Define the routine** as an `abiFrameProg` flatten and byte-tie it:
     ```
     def fooProg : List Instr := abiFrameProg negImm posImm fooFrame fooBody
     def fooProgList : List Instr := [ …spelled out… ]
     #guard fooProg = fooProgList          -- byte-transparency
     theorem fooProg_eq : fooProg = fooProgList := rfl
     def fooCr : CodeReq := CodeReq.ofProg BASE fooProgList
     ```
     (For a re-emitted drop-in, `fooProgList` must also equal the emitted
     `Program` by `rfl`, and ziskemu/EEST A/B parity vs the old bytes is
     mandatory — see `ParentHeaderFrame.lean` / PR #9975.)

  2. **State the genuine post** (unweakened: the routine's full semantics) and
     prove the **body triple** — the only bespoke work.  Straight-line pieces
     go through `runBlock` over an `ofProg` slice lifted with `lift_code`;
     an internal countdown loop through `countdown_loop`; a cross-call
     through `frame_call` (callee contract = any whole-routine
     `cpsTripleWithin` at `ret := A + 4`, e.g. another `abi_frame` port).

  3. **Wrap with `abi_frame posImm halign hbody`**: applies `abiFrame_spec` and discharges
     all twelve routine side-conditions (`hframe`/`hne`/`hbound`/
     `hprogBound`/`hret`/`halign`/`hframeRestore`/`hcpF`/`hcpF'`/`hsub`)
     automatically, leaving nothing.  The goal must be the standard
     `abiFrame_spec` conclusion shape (see `AbiFrameLoopDemo.mulFrame_spec`).

  4. `#print axioms` the result — it must be `[propext, Classical.choice,
     Quot.sound]`.  The tactics build genuine proof terms only (`decide`/
     `rfl`/`omega`/lemma application); nothing is admitted.

  ## What the tactics close vs what you supply

  | goal | tactic | closes |
  |---|---|---|
  | `P.pcFree` over `**`/`↦ᵣ`/`↦ₘ`/`memOwn`/`regOwn`/`⌜⌝`/`bytesRegion`/`stackFree`/`regsAt`/`frameSlots*` | `pcf` | always |
  | `∀ a i, singleton/ofProg … = some i → cr a = some i` (concrete) | `code_mem` | always |
  | lift a slice/loop triple into the routine `CodeReq` | `lift_code h` | always |
  | whole-routine wrap + its 12 side-conditions | `abi_frame posImm halign hbody` | all but `hbody` |
  | countdown loop + its 5 side-conditions | `countdown_loop exitOff hbody` | all but the per-iteration `hbody` |
  | one `jal ra` call + its 4 side-conditions | `frame_call offset hcallee` | all but the callee contract |
  | the body triple, loop invariant, genuine post | — | **you** (this IS the proof) |

  Zero soundness surface: every tactic assembles existing kernel-checked
  lemmas; no axioms, no `sorry`, no `native_decide`/`bv_decide`.

  ## Worked examples (read in this order)

  * `AbiFrameLoopDemo.mulFrame_spec` — leaf + internal loop
    (`countdown_loop` + `abi_frame`).
  * `AbiFrameCallDemo.twiceFrame_spec` — cross-calls (`abiFrameCall_spec` +
    `abi_frame`), callee with its own frame carved from `stackFree`.
  * `Codegen/Programs/Bn254Fq12SetOneSAsm.lean` — a REAL guest routine,
    byte-transparent: flat callee contract (`bnqZeroFlat_spec`, bottom-test
    loop via `countdownLoopBottom_spec` over the writable `dwordsIs` region)
    consumed by `callWithin_spec` inside an `abi_frame` wrap.

  Known limits: `abi_frame` at very large scale (the 84-instruction
  `ParentHeaderFrame` routine) hits elaboration limits in the automated
  side-condition search — such routines keep the explicit `abiFrame_spec`
  application (same statement, spelled side-conditions).  `runBlock` chains
  single-instruction specs; multi-instruction sub-triples (a lifted loop, a
  call) compose with `cpsTripleWithin_frameR` + `…_seq_perm_same_cr` as in
  the worked examples.
-/

import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.AbiFrameLoopBottom
import EvmAsm.Rv64.MemRegion

namespace EvmAsm.Rv64
namespace SAsm

-- ============================================================================
-- Code-membership by evaluation.
-- ============================================================================

/-- Slice containment by pointwise lookup: if every slot of the (concrete)
    slice `seg` at `A` is already mapped by `cr`, then `ofProg A seg ⊆ cr`.
    The hypothesis is decidable for concrete data, so `code_mem` discharges
    it with `decide` — replacing the manual `ofProg_mono_sub` index/range
    plumbing. -/
theorem CodeReq.sub_ofProg_of_lookup {cr : CodeReq} (A : Word) (seg : List Instr)
    (hbound : 4 * seg.length < 2 ^ 64)
    (h : ∀ k, (hk : k < seg.length) →
      cr (A + BitVec.ofNat 64 (4 * k)) = some (seg.get ⟨k, hk⟩)) :
    ∀ a i, CodeReq.ofProg A seg a = some i → cr a = some i := by
  intro a i hai
  obtain ⟨k, hk, rfl⟩ := ofProg_some_range hai
  have hl := CodeReq.ofProg_lookup_addr A seg k (A + BitVec.ofNat 64 (4 * k)) hk hbound rfl
  have hi : i = seg.get ⟨k, hk⟩ := Option.some.inj (hai.symm.trans hl)
  rw [hi]
  exact h k hk

/-- `code_mem` closes concrete code-membership goals
    `∀ a i, (singleton addr instr / ofProg A seg) a = some i → cr a = some i`
    by evaluation: identity, a `singleton_mono` point lookup, or the
    pointwise slice lookup — all via `decide` on the concrete `CodeReq`. -/
macro "code_mem" : tactic =>
  `(tactic| first
    | (with_reducible exact fun a i h => h)
    | (with_reducible exact CodeReq.singleton_mono (by decide))
    | (with_reducible exact CodeReq.sub_ofProg_of_lookup _ _ (by decide) (by decide)))

-- ============================================================================
-- pcFree automation.
-- ============================================================================

/-- `pcf` closes `P.pcFree` for any assertion built from the standard atoms
    and the frame/region/stack combinators. -/
macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact pcFree_instrAt
      | exact bytesRegion_pcFree _ _
      | exact pcFree_stackFree _ _
      | exact pcFree_dwordsIs _ _
      | exact pcFree_regsAt _ _
      | exact pcFree_frameSlotsOwn _ _
      | exact pcFree_frameSlotsSaved _ _ _
      | exact pcFree_regFileIs _)

-- ============================================================================
-- Address-bridge helpers.
-- ============================================================================

/-- The frame-restore side-condition, reduced to a `decide`-able immediate
    fact (`sext negImm + sext posImm = 0`), for a FREE `sp0`. -/
theorem sext_frameRestore (sp0 : Word) (negImm posImm : BitVec 12)
    (h : signExtend12 negImm + signExtend12 posImm = 0) :
    (sp0 + signExtend12 negImm) + signExtend12 posImm = sp0 := by
  rw [BitVec.add_assoc, h]
  exact BitVec.add_zero sp0

-- ============================================================================
-- The wrappers.
-- ============================================================================

/-- Term-form lift with the triple FIRST (so the containment side-goal
    elaborates with the sub-`CodeReq` already pinned): use
    `liftCode (cr' := routineCr) h (by code_mem)`.  The `lift_code h` tactic
    below is the goal-directed form. -/
theorem liftCode {nSteps : Nat} {entry exit_ : Word} {cr cr' : CodeReq}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_ cr P Q)
    (hmono : ∀ a i, cr a = some i → cr' a = some i) :
    cpsTripleWithin nSteps entry exit_ cr' P Q :=
  cpsTripleWithin_extend_code hmono h

/-- `lift_code h` lifts a triple proven over a sub-`CodeReq` (an `ofProg`
    slice, a loop core at its anchor, …) into the goal's routine `CodeReq`,
    discharging the containment by evaluation. -/
macro "lift_code" h:term : tactic =>
  `(tactic| (refine cpsTripleWithin_extend_code ?_ $h; code_mem))

/-- `abi_frame posImm halign hbody` closes a whole-routine goal in the
    standard `abiFrame_spec` conclusion shape, given the frame-release
    immediate, the return-address alignment fact, and the single-exit body
    triple `hbody` (which pins `body`/`bodySteps`/`vals'`): all other
    side-conditions are discharged automatically. -/
macro "abi_frame" posImm:term:max halign:term:max hbody:term:max : tactic =>
  `(tactic| exact abiFrame_spec
      (posImm := $posImm)
      (hframe := rfl)
      (hne := by decide)
      (hbound := by decide)
      (hprogBound := by decide)
      (hret := rfl)
      (halign := $halign)
      (hframeRestore := sext_frameRestore _ _ _ (by decide))
      (hcpF := by pcf)
      (hcpF' := by pcf)
      (hsub := by code_mem)
      (hbody := $hbody))

/-- `countdown_loop hbody` closes a whole-loop goal in the
    `countdownLoop_spec` conclusion shape, given the per-iteration body
    triple family `hbody : ∀ n, n < N → …`: guard membership, exit address,
    counter bound, and the invariant's `pcFree` are discharged
    automatically. -/
macro "countdown_loop" exitOff:term:max hbody:term:max : tactic =>
  `(tactic| exact countdownLoop_spec (exitOff := $exitOff) (cr := _) (hdr := _)
      (exitAddr := _) (ctr := _) (bodyStep := _) (N := _) (inv := _)
      (_hctr_ne := by decide)
      (hNbound := by first | assumption | exact BitVec.isLt _ | omega)
      (hexit := by decide)
      (hpcFree := fun n => by pcf)
      (hguardMem := by code_mem)
      (hbody := $hbody))

/-- `countdown_loop_bottom backOff hbody` — the do-while analogue of
    `countdown_loop`, closing a `countdownLoopBottom_spec`-shaped goal given
    the per-iteration body triple family. -/
macro "countdown_loop_bottom" backOff:term:max hbody:term:max : tactic =>
  `(tactic| exact countdownLoopBottom_spec (backOff := $backOff) (cr := _)
      (hdr := _) (tst := _) (ctr := _) (bodyStep := _) (N := _) (inv := _)
      (_hctr_ne := by decide)
      (hN1 := by first | assumption | omega)
      (hNbound := by first | assumption | exact BitVec.isLt _ | omega)
      (hback := by decide)
      (hpcFree := fun n => by pcf)
      (hguardMem := by code_mem)
      (hbody := $hbody))

/-- `frame_call hcallee` closes a single-call goal in the
    `abiFrameCall_spec` conclusion shape, given the callee's whole-routine
    contract `hcallee` (at `ret := A + 4`): the `jal` target arithmetic,
    call-site code membership, and `pcFree` side-conditions are discharged
    automatically. -/
macro "frame_call" offset:term:max hcallee:term:max : tactic =>
  `(tactic| exact abiFrameCall_spec (offset := $offset)
      (htarget := by decide)
      (hmem := by code_mem)
      (hpre := by pcf)
      (hF := by pcf)
      (hcallee := $hcallee))

end SAsm
end EvmAsm.Rv64
