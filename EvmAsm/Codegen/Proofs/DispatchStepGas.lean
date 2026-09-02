/-
  EvmAsm.Codegen.Proofs.DispatchStepGas

  **The per-opcode gas debit of the shipped dispatcher loop, as a machine
  triple at its linked address** (GH #13173, obligation 4).

  ## What this is

  `dispatchLoopBody_prog` (`Codegen/Dispatch.lean`) is the sixteen-instruction
  fetch / charge / dispatch body of `emitRuntimeDispatcherLoop`, tied to the
  SHIPPED emitter text by `dispatchLoopFunction_eq_prog` (`rfl`) composed with
  `emitRuntimeDispatcherLoop_split`.  #13178 gave it a linker symbol of its own
  (`.dispatch_loop_body`), rebased the Program onto it, and registered
  `(GuestAddrs.dispatch_loop_body, dispatchLoopBody_prog)` in
  `guestImageEntries`.  That is what makes the `CodeReq.ofProg` below
  attachable, and `dispatchLoopBody_block_sub` is what lifts a triple stated
  over it into `guestImageCodeReq`.

  This file spends that anchor on the **M30 static-gas charge**, indices 6..10:

      idx  6  (+24)   ld   x7, 568(x20)        -- x7 := env.gasRemaining
      idx  7  (+28)   bgeu x7, x6, +8          -- relaxed head of the source
      idx  8  (+32)   jal  x0, .exit_outofgas  --   `bltu x7, x6, .exit_outofgas`
      idx  9  (+36)   sub  x7, x7, x6
      idx 10  (+40)   sd   x7, 568(x20)        -- env.gasRemaining -= cost

  `dispatchStep_gasDebit_within` is a two-exit `cpsBranchWithin 5` over exactly
  those five instructions: it debits `env+568` by whatever cost the previous
  block left in `x6` when the gas suffices, and otherwise leaves the loop for
  the LINKED `GuestAddrs.exit_outofgas` with the cell untouched.  The
  discriminating fact `BitVec.ult gas cost` is carried as a pure atom on each
  arm, so the two exits are distinguished rather than merely both offered.

  ⚠️ Indices 7 and 8 are ONE source line.  `dispatchLoopBody_relocs` records
  `(7, .br .bltu .x7 .x6 ".exit_outofgas")`: the assembler relaxed the
  out-of-range `bltu` into an inverted `BGEU` skipping 8 bytes plus a `JAL`.
  So the BGEU-**taken** edge is the has-enough-gas path and the fall-through is
  the out-of-gas path — the opposite reading of the source mnemonic.  The step
  bound 5 counts both halves of the relaxed pair, but no execution runs both.

  ## What this is NOT: the 348-byte code-size stop guard

  ⛔ This is a triple for a **fragment of the loop body**, not for one iteration
  of the loop.  `emitRuntimeDispatcherLoop` is
  `dispatchLoopEntryAsm ++ emitDispatchLoopCodeSizeStopGuard depthAwareStop ++
  dispatchLoopFunction ++ emitDispatchResume`, and the guard occupies the whole
  348 bytes between `.dispatch_loop` and `.dispatch_loop_body`.  A one-iteration
  lemma has to cross it; this one does not, because its entry `+24` is already
  inside the body and the guard is not in the extent at all.  Framing it out is
  therefore not an argument that needs making — the `CodeReq` here is the body's
  own `ofProg`, which constrains the 64 bytes
  `[.dispatch_loop_body, .dispatch_resume)` and asserts nothing whatever about
  the 348 before them.  See `dispatch_loop_head_not_covered` below, which
  states that boundary as a theorem rather than as prose.

  What a one-iteration lemma would additionally cost is measured in the
  docstring of `dispatch_loop_head_not_covered`.

  ## Non-vacuity

  `dispatchStep_gasDebit_instance` instantiates the whole statement at the
  linked `GuestAddrs.evm_env` with a real `staticGasCost` entry, and separately
  witnesses that the gas cell is an addressable aligned dword — i.e. the `↦ₘ`
  in the precondition is satisfiable, not a false assertion about a bad address.
  `dispatchStep_gasDebit_premises_refutable` is the negative control: three
  conjuncts, each a hypothesis of the family that is provably FALSE at a
  concrete point — the head-anchored code premise (this is #13178's 348-byte
  finding restated as a premise), the sufficient-gas premise, and the
  precondition's own memory atom at a misaligned environment pointer.
-/
import EvmAsm.Codegen.Proofs.GuestImage
import EvmAsm.Rv64.SAsm.FramePort

namespace EvmAsm.Codegen.DispatchStepGas

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-- The loop body's linked entry, as a machine word.  Read from `GuestAddrs`,
    never spelled: `dispatch_loop_body` is `0x800307d8`, 348 bytes past the
    loop head. -/
abbrev B : Word := BitVec.ofNat 64 GuestAddrs.dispatch_loop_body

/-- The body's own image block — the `CodeReq` #13178 made attachable.  Every
    instruction cited below is pulled out of it by `code_mem`, and
    `dispatchLoopBody_block_sub` transports the finished triple into
    `guestImageCodeReq`. -/
abbrev dlbCode : CodeReq := CodeReq.ofProg B dispatchLoopBody_prog

/-- The relaxed jump's immediate, taken from the Program rather than restated:
    idx 8 is `.JAL .x0 (jalOff GuestAddrs.exit_outofgas (dispatch_loop_body + 32))`. -/
abbrev oogOff : BitVec 21 :=
  jalOff GuestAddrs.exit_outofgas (GuestAddrs.dispatch_loop_body + 32)

/-! ### Extent cross-checks, derived from the symbol table

    `prog.length * 4` against the gap between two NAMED linker symbols.  Both
    halves are kernel-checked; neither reads a digit out of prose. -/

theorem body_length : dispatchLoopBody_prog.length = 16 := rfl

theorem body_extent :
    GuestAddrs.dispatch_resume - GuestAddrs.dispatch_loop_body
      = 4 * dispatchLoopBody_prog.length := by
  rw [body_length]; decide

/-- The guard's size, likewise derived: the whole gap between the loop head and
    the body is the `depthAwareStop` code-size stop guard. -/
theorem guard_extent :
    GuestAddrs.dispatch_loop_body - GuestAddrs.dispatch_loop = 348 := by decide

/-! ### Two local branch/triple splices

    `cpsBranchWithin_seq_cpsTripleWithin_{taken,notTaken}` in the dependency
    both union two `CodeReq`s and demand they be disjoint; here everything
    lives under the single `dlbCode`, so the same-`cr` forms are what compose.
    Derived from the dependency's `_same_cr` primitive by `cpsBranchWithin_swap`
    rather than re-proved. -/

theorem seq_taken_same_cr {n1 n2 : Nat} {entry mid target exit_f : Word}
    {cr : CodeReq} {P Q_t1 Q_f1 Q_t2 : Assertion}
    (h1 : cpsBranchWithin n1 entry cr P mid Q_t1 exit_f Q_f1)
    (h2 : cpsTripleWithin n2 mid target cr Q_t1 Q_t2) :
    cpsBranchWithin (n1 + n2) entry cr P target Q_t2 exit_f Q_f1 :=
  cpsBranchWithin_swap
    (cpsBranchWithin_seq_cpsTripleWithin_same_cr (cpsBranchWithin_swap h1) h2
      (fun _ hp => hp))

theorem seq_ntaken_same_cr {n1 n2 : Nat} {entry mid target exit_t : Word}
    {cr : CodeReq} {P Q_t Q_f1 Q_f2 : Assertion}
    (h1 : cpsBranchWithin n1 entry cr P exit_t Q_t mid Q_f1)
    (h2 : cpsTripleWithin n2 mid target cr Q_f1 Q_f2) :
    cpsBranchWithin (n1 + n2) entry cr P exit_t Q_t target Q_f2 :=
  cpsBranchWithin_swap (seq_taken_same_cr (cpsBranchWithin_swap h1) h2)

set_option maxRecDepth 8000

/-- **The dispatch step's gas debit** (#13173, obligation 4).

    Five instructions of the shipped dispatcher loop body at their linked
    addresses.  `gp` is the environment pointer in `x20`, `cost` is whatever the
    preceding `opcode_gas_costs` load left in `x6`, `gas` is the dword currently
    at `env+568`, and `old7` is `x7`'s incoming value (clobbered by the load).

    * **enough gas** (`¬ gas <ᵤ cost`): exits at `+44`, the instruction after
      the store, with `env+568` holding `gas - cost` and `x7` mirroring it.
      `+44` is index 11, the `auipc` that starts the handler-table load — so
      this is the arm that continues into the dispatch.
    * **out of gas** (`gas <ᵤ cost`): exits at the LINKED
      `GuestAddrs.exit_outofgas`, with `env+568` UNCHANGED.  That the failing
      path leaves the gas cell alone is part of the statement, not a remark.

    The `cost` register is left free: this lemma is about the debit, and says
    nothing about `opcode_gas_costs` (that table's load is indices 2..5, and its
    own read spec is `Proofs/OpcodeTables.lean`). -/
theorem dispatchStep_gasDebit_within (gp cost gas old7 : Word) :
    cpsBranchWithin 5 (B + 24) dlbCode
      ((((.x20 : Reg) ↦ᵣ gp) ** ((.x7 : Reg) ↦ᵣ old7) ** ((gp + 568) ↦ₘ gas))
        ** ((.x6 : Reg) ↦ᵣ cost))
      (B + 44)
        ((((.x20 : Reg) ↦ᵣ gp) ** ((.x7 : Reg) ↦ᵣ (gas - cost))
            ** ((gp + 568) ↦ₘ (gas - cost)))
          ** ⌜¬ BitVec.ult gas cost⌝ ** ((.x6 : Reg) ↦ᵣ cost))
      (BitVec.ofNat 64 GuestAddrs.exit_outofgas)
        (((((.x7 : Reg) ↦ᵣ gas) ** ((.x6 : Reg) ↦ᵣ cost) ** ⌜BitVec.ult gas cost⌝))
          ** (((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas))) := by
  -- idx 6 (+24): ld x7, 568(x20).
  have hld := ld_spec_gen_within .x7 .x20 gp old7 gas (568 : BitVec 12) (B + 24)
    (by decide)
  rw [show signExtend12 (568 : BitVec 12) = (568 : Word) from by decide,
      show (B + 24 : Word) + 4 = B + 28 from by decide] at hld
  have hldC := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR (((.x6 : Reg) ↦ᵣ cost)) (by pcf) hld) (by code_mem)
  -- idx 7 (+28): bgeu x7, x6, +8 — taken means the gas suffices.
  have hbr := bgeu_spec_gen_within .x7 .x6 (8 : BitVec 13) gas cost (B + 28)
  rw [show (B + 28 : Word) + signExtend13 (8 : BitVec 13) = B + 36 from by decide,
      show (B + 28 : Word) + 4 = B + 32 from by decide] at hbr
  have hbrC := cpsBranchWithin_extend_code (cr' := dlbCode) (by code_mem)
    (cpsBranchWithin_frameR (((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas))
      (by pcf) hbr)
  have hsplit := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hldC hbrC
  -- idx 9 (+36), idx 10 (+40): sub x7, x7, x6 ; sd x7, 568(x20).
  have hsub := sub_spec_gen_rd_eq_rs1_within .x7 .x6 gas cost (B + 36) (by decide)
  rw [show (B + 36 : Word) + 4 = B + 40 from by decide] at hsub
  have hsd := sd_spec_gen_within .x20 .x7 gp (gas - cost) gas (568 : BitVec 12)
    (B + 40)
  rw [show signExtend12 (568 : BitVec 12) = (568 : Word) from by decide,
      show (B + 40 : Word) + 4 = B + 44 from by decide] at hsd
  have hsubC := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR
      (⌜¬ BitVec.ult gas cost⌝ ** ((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas))
      (by pcf) hsub) (by code_mem)
  have hsdC := liftCode (cr' := dlbCode)
    (cpsTripleWithin_frameR (⌜¬ BitVec.ult gas cost⌝ ** ((.x6 : Reg) ↦ᵣ cost))
      (by pcf) hsd) (by code_mem)
  have hdebit := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)
    hsubC hsdC
  have hdebit' := cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq) hdebit
    (P' := (((.x7 : Reg) ↦ᵣ gas) ** ((.x6 : Reg) ↦ᵣ cost) ** ⌜¬ BitVec.ult gas cost⌝)
             ** (((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas)))
  have htaken := seq_taken_same_cr hsplit hdebit'
  -- idx 8 (+32): jal x0, .exit_outofgas — the relaxed bltu's long-jump tail.
  have hjal := jal_x0_spec_gen_within oogOff (B + 32)
  rw [show (B + 32 : Word) + signExtend21 oogOff
        = BitVec.ofNat 64 GuestAddrs.exit_outofgas from by decide] at hjal
  have hjalF := cpsTripleWithin_frameL
    ((((.x7 : Reg) ↦ᵣ gas) ** ((.x6 : Reg) ↦ᵣ cost) ** ⌜BitVec.ult gas cost⌝)
      ** (((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas))) (by pcf) hjal
  rw [sepConj_emp_right'] at hjalF
  exact seq_ntaken_same_cr htaken (liftCode (cr' := dlbCode) hjalF (by code_mem))

/-- **The same statement inside the whole-image `CodeReq`.**  This is the
    payoff of #13178 and the thing that did not exist before it: the triple is
    stated over the body's `ofProg`, and `dispatchLoopBody_block_sub` — which
    exists only because `(GuestAddrs.dispatch_loop_body, dispatchLoopBody_prog)`
    is a `guestImageEntries` row — transports it verbatim into
    `guestImageCodeReq`, so it composes with anything else stated against the
    emitted image. -/
theorem dispatchStep_gasDebit_image (gp cost gas old7 : Word) :
    cpsBranchWithin 5 (B + 24) guestImageCodeReq
      ((((.x20 : Reg) ↦ᵣ gp) ** ((.x7 : Reg) ↦ᵣ old7) ** ((gp + 568) ↦ₘ gas))
        ** ((.x6 : Reg) ↦ᵣ cost))
      (B + 44)
        ((((.x20 : Reg) ↦ᵣ gp) ** ((.x7 : Reg) ↦ᵣ (gas - cost))
            ** ((gp + 568) ↦ₘ (gas - cost)))
          ** ⌜¬ BitVec.ult gas cost⌝ ** ((.x6 : Reg) ↦ᵣ cost))
      (BitVec.ofNat 64 GuestAddrs.exit_outofgas)
        (((((.x7 : Reg) ↦ᵣ gas) ** ((.x6 : Reg) ↦ᵣ cost) ** ⌜BitVec.ult gas cost⌝))
          ** (((.x20 : Reg) ↦ᵣ gp) ** ((gp + 568) ↦ₘ gas))) :=
  cpsBranchWithin_extend_code dispatchLoopBody_block_sub
    (dispatchStep_gasDebit_within gp cost gas old7)

/-! ### Non-vacuity -/

/-- **Satisfiable instance.**  The family is instantiated at the linked
    environment pointer with a real `staticGasCost` entry (`0x01` = ADD), and
    the second conjunct witnesses that the precondition's memory atom is not a
    false assertion about a bad address: `env+568` is an addressable, aligned
    dword.  (`memIs` bakes `isValidDwordAccess` in — `SepLogic.lean` — so a
    misaligned or out-of-range `gp` makes the precondition FALSE rather than
    merely unusable; see the third conjunct of the control below.) -/
theorem dispatchStep_gasDebit_instance :
    (∀ old7 : Word,
      cpsBranchWithin 5 (B + 24) guestImageCodeReq
        ((((.x20 : Reg) ↦ᵣ (BitVec.ofNat 64 GuestAddrs.evm_env))
            ** ((.x7 : Reg) ↦ᵣ old7)
            ** ((BitVec.ofNat 64 GuestAddrs.evm_env + 568) ↦ₘ (1000 : Word)))
          ** ((.x6 : Reg) ↦ᵣ (BitVec.ofNat 64 (staticGasCost 0x01))))
        (B + 44)
          ((((.x20 : Reg) ↦ᵣ (BitVec.ofNat 64 GuestAddrs.evm_env))
              ** ((.x7 : Reg) ↦ᵣ ((1000 : Word)
                    - BitVec.ofNat 64 (staticGasCost 0x01)))
              ** ((BitVec.ofNat 64 GuestAddrs.evm_env + 568) ↦ₘ ((1000 : Word)
                    - BitVec.ofNat 64 (staticGasCost 0x01))))
            ** ⌜¬ BitVec.ult (1000 : Word) (BitVec.ofNat 64 (staticGasCost 0x01))⌝
            ** ((.x6 : Reg) ↦ᵣ (BitVec.ofNat 64 (staticGasCost 0x01))))
        (BitVec.ofNat 64 GuestAddrs.exit_outofgas)
          (((((.x7 : Reg) ↦ᵣ (1000 : Word))
              ** ((.x6 : Reg) ↦ᵣ (BitVec.ofNat 64 (staticGasCost 0x01)))
              ** ⌜BitVec.ult (1000 : Word)
                    (BitVec.ofNat 64 (staticGasCost 0x01))⌝))
            ** (((.x20 : Reg) ↦ᵣ (BitVec.ofNat 64 GuestAddrs.evm_env))
              ** ((BitVec.ofNat 64 GuestAddrs.evm_env + 568) ↦ₘ (1000 : Word)))))
    ∧ isValidDwordAccess (BitVec.ofNat 64 GuestAddrs.evm_env + 568) = true
    ∧ ¬ BitVec.ult (1000 : Word) (BitVec.ofNat 64 (staticGasCost 0x01))
    ∧ (1000 : Word) - BitVec.ofNat 64 (staticGasCost 0x01) = (997 : Word) :=
  ⟨fun old7 => dispatchStep_gasDebit_image _ _ _ old7, by decide, by decide, by decide⟩

set_option maxRecDepth 40000 in
/-- **Negative control.**  Three hypotheses of the family above, each provably
    FALSE at a concrete point — so none of them is idle decoration.

    1. **The code premise at the loop HEAD is refuted.**  Re-anchoring the same
       Program 348 bytes earlier, at `.dispatch_loop`, would put a
       `ld x7, 568(x20)` at `dispatch_loop + 24`; the shipped image has code-size
       stop-guard bytes there instead.  This is #13178's finding stated as a
       premise of *this* lemma: the whole triple would be unsupported at the
       pre-#13173 anchor, and `cpsTripleWithin_needs_entry_code` makes an
       unpinned entry UNSATISFIABLE rather than weak.
    2. **The sufficient-gas premise discriminates.**  At `gas = 2`, `cost = 3`
       the taken arm's `⌜¬ gas <ᵤ cost⌝` is false, so the two exits are not both
       reachable from one state.
    3. **The precondition's memory atom can be FALSE.**  At a misaligned
       environment pointer the `↦ₘ` at `gp + 568` is unsatisfiable, which is
       what makes the aligned witness in `dispatchStep_gasDebit_instance` worth
       stating. -/
theorem dispatchStep_gasDebit_premises_refutable :
    guestImageCodeReq (BitVec.ofNat 64 GuestAddrs.dispatch_loop + 24)
        ≠ some (.LD .x7 .x20 (568 : BitVec 12))
    ∧ ¬ (¬ BitVec.ult (2 : Word) (3 : Word))
    ∧ isValidDwordAccess ((3 : Word) + 568) = false := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (BitVec.ofNat 64 GuestAddrs.dispatch_loop + 24 : Word)
        = BitVec.ofNat 64 (GuestAddrs.dispatch_loop + 24) from by decide]
  decide

/-! ### The boundary this lemma does not cross -/

/-- **The 348-byte code-size stop guard is outside the extent, as a theorem.**

    `emitRuntimeDispatcherLoop` is `dispatchLoopEntryAsm ++
    emitDispatchLoopCodeSizeStopGuard depthAwareStop ++ dispatchLoopFunction ++
    emitDispatchResume` (`emitRuntimeDispatcherLoop_split`), and `.dispatch_loop`
    is the last label of the first factor, so every byte from the head to
    `.dispatch_loop_body` belongs to the guard.  `dlbCode` resolves at NO
    address below `B`: the triple above therefore neither uses nor constrains
    the guard, and framing it out required no argument — it was never in scope.

    ⭐ **What a one-iteration lemma would still cost, measured.**  The guard is
    87 instructions in the shipped `depthAwareStop := true` arm, but its
    *hot path is three*: `sub x5, x10, x21`, `ld x6, 496(x20)`,
    `bltu x5, x6, 1f` — and `1:` is the very label `.dispatch_loop_body` sits
    on, so the in-range branch falls straight into `B`.  The remaining ~84
    instructions are the EOF-halt route, entered only when the code pointer has
    run past `env.codeSize`.  So a head-to-body triple under an in-range premise
    is a THREE-instruction obligation, not a 348-byte one; what is genuinely
    expensive is the halt route, and it is expensive for a reason that is not
    transcription: it calls `frame_return` through `ra` and jumps into the
    CREATE deposit-from-halt path, i.e. it needs two callee contracts before it
    can be a triple at all.  (Both targets are named in prose only, and
    deliberately not spelled as call syntax: `scripts/transcription_queue.py`
    scrapes `jal ra, <sym>` out of any source line, so writing the instruction
    out here would score a phantom call site and move the queue.)  Converting it is
    therefore a contract problem, and it is NOT named as a blocked-on symbol
    anywhere in `Progress/Obligations.lean` — nobody is blocked on the halt
    route; the in-range path is what a dispatch-step lemma needs. -/
theorem dispatch_loop_head_not_covered :
    dlbCode (BitVec.ofNat 64 GuestAddrs.dispatch_loop) = none
    ∧ dlbCode (BitVec.ofNat 64 (GuestAddrs.dispatch_loop_body - 4)) = none
    ∧ GuestAddrs.dispatch_loop_body - GuestAddrs.dispatch_loop = 348 := by
  decide

end EvmAsm.Codegen.DispatchStepGas
