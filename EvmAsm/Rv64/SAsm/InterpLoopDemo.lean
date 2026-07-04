/-
  EvmAsm.Rv64.SAsm.InterpLoopDemo

  The interpreter-loop pilot (bead evm-asm-4ch8f.10, strategy in
  docs/4ch8f-interp-strategy.md): a minimal end-to-end fetch-charge-dispatch
  loop over a 3-opcode toy ISA (PUSH imm8 / ADD / STOP-or-invalid), proven
  to simulate a Lean-side step function `toyStep`.

  The pilot exercises exactly the composition risks of the real dispatch
  loop (EvmAsm/Codegen/Dispatch.lean:2404):

  - `Stmt.whileS` for the loop, with the *initial gas carried by the loop
    entry snapshot*: the invariant names the spec trace
    `toyRun prog (ToyState.init (rf₀.get .x29).toNat) i` — per-execution
    constants reach the invariant only through the snapshot, the way the
    real loop's env/frame constants must.
  - `Stmt.callRegS` for dispatch into three *real* handler `Fn`s through a
    runtime-selected register, with one uniform `.pre` VC.  The handler
    contracts are snapshot-parameterized (`FnHandleS`): each post pins the
    exit registers/window as functions of the *entry* state, which is what
    lets one fixed call site transform an evolving machine state.
  - Gas as the variant: the loop body charges 1 gas per iteration before
    dispatch; the fuel is a static cap with `gas₀ < cap`, and the
    `exhausted` VC closes from the spec-side lemma `gas + i = gas₀` —
    wrong caps are unprovable, never unsound.
  - The value stack is a grow-down window in the function's rw region
    (top at `x12`, exactly the real dispatcher's `x12` convention), with
    handlers reading/writing it through the shared region contract.

  Spec-side safety (`ToyState.ok` along the trace) replaces the real
  dispatcher's stack/pc guard exits; the guards are ordinary `when`
  blocks and belong to the dispatch-skeleton bead (.49).
-/

import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64
namespace SAsm
namespace InterpLoopDemo

/- The engine-normalization proofs deliberately reuse one uniform
   `simp only` set (register-file get/set, `signExtend12` constants,
   address collapse); per-site pruning would make the ~20 call sites
   fragile against instruction-list edits. -/
set_option linter.unusedSimpArgs false

open Stmt

-- ============================================================================
-- The toy ISA, spec side
-- ============================================================================

/-- The Lean-side machine state the loop invariant relates the RISC-V
    state to: value stack (top first), program counter, gas, halt flag. -/
structure ToyState where
  stack : List Word
  pc : Nat
  gas : Nat
  halted : Bool

/-- Initial state: empty stack, pc 0, full gas, running. -/
def ToyState.init (gas₀ : Nat) : ToyState := ⟨[], 0, gas₀, false⟩

/-- One fetch-charge-dispatch step.  Opcode 1 = PUSH imm8, 2 = ADD,
    anything else halts (STOP and invalid alike).  Charging precedes
    dispatch: at gas 0 the machine halts without executing.  A halted
    state is a fixed point. -/
def toyStep (prog : List (BitVec 8)) (σ : ToyState) : ToyState :=
  if σ.halted then σ
  else if σ.gas = 0 then { σ with halted := true }
  else
    let op := prog.getD σ.pc 0
    if op = 1 then
      { stack := (prog.getD (σ.pc + 1) 0).zeroExtend 64 :: σ.stack,
        pc := σ.pc + 2, gas := σ.gas - 1, halted := false }
    else if op = 2 then
      match σ.stack with
      | a :: b :: rest =>
          { stack := (a + b) :: rest, pc := σ.pc + 1,
            gas := σ.gas - 1, halted := false }
      | _ => { σ with halted := true }
    else
      { σ with gas := σ.gas - 1, halted := true }

/-- The spec trace: `i` steps from `σ₀`. -/
def toyRun (prog : List (BitVec 8)) (σ₀ : ToyState) : Nat → ToyState
  | 0 => σ₀
  | n + 1 => toyStep prog (toyRun prog σ₀ n)

theorem toyStep_halted {prog : List (BitVec 8)} {σ : ToyState}
    (h : σ.halted = true) : toyStep prog σ = σ := by
  simp [toyStep, h]

theorem toyStep_oog {prog : List (BitVec 8)} {σ : ToyState}
    (h1 : σ.halted = false) (h2 : σ.gas = 0) :
    toyStep prog σ = { σ with halted := true } := by
  simp [toyStep, h1, h2]

theorem toyStep_push {prog : List (BitVec 8)} {σ : ToyState}
    (h1 : σ.halted = false) (h2 : σ.gas ≠ 0)
    (hop : prog.getD σ.pc 0 = 1) :
    toyStep prog σ
      = { stack := (prog.getD (σ.pc + 1) 0).zeroExtend 64 :: σ.stack,
          pc := σ.pc + 2, gas := σ.gas - 1, halted := false } := by
  have hop' : prog[σ.pc]?.getD 0#8 = 1#8 := hop
  simp [toyStep, h1, h2, hop']

theorem toyStep_add {prog : List (BitVec 8)} {σ : ToyState}
    {a b : Word} {rest : List Word}
    (h1 : σ.halted = false) (h2 : σ.gas ≠ 0)
    (hop1 : prog.getD σ.pc 0 ≠ 1) (hop2 : prog.getD σ.pc 0 = 2)
    (hstack : σ.stack = a :: b :: rest) :
    toyStep prog σ
      = { stack := (a + b) :: rest, pc := σ.pc + 1,
          gas := σ.gas - 1, halted := false } := by
  have hop1' : ¬ prog[σ.pc]?.getD 0#8 = 1#8 := hop1
  have hop2' : prog[σ.pc]?.getD 0#8 = 2#8 := hop2
  simp [toyStep, h1, h2, hop1', hop2', hstack]

theorem toyStep_stop {prog : List (BitVec 8)} {σ : ToyState}
    (h1 : σ.halted = false) (h2 : σ.gas ≠ 0)
    (hop1 : prog.getD σ.pc 0 ≠ 1) (hop2 : prog.getD σ.pc 0 ≠ 2) :
    toyStep prog σ = { σ with gas := σ.gas - 1, halted := true } := by
  have hop1' : ¬ prog[σ.pc]?.getD 0#8 = 1#8 := hop1
  have hop2' : ¬ prog[σ.pc]?.getD 0#8 = 2#8 := hop2
  simp [toyStep, h1, h2, hop1', hop2']

/-- Halted states freeze: the trace is constant past its halt point. -/
theorem toyRun_halted_of_le {prog : List (BitVec 8)} {σ₀ : ToyState}
    {i j : Nat} (hij : i ≤ j)
    (h : (toyRun prog σ₀ i).halted = true) :
    toyRun prog σ₀ j = toyRun prog σ₀ i := by
  induction j with
  | zero =>
      obtain rfl : i = 0 := by omega
      rfl
  | succ j ih =>
      by_cases hj : i = j + 1
      · subst hj; rfl
      · have hle : i ≤ j := by omega
        have hj' := ih hle
        show toyStep prog (toyRun prog σ₀ j) = _
        rw [hj', toyStep_halted h]

theorem exists_two_cons' {l : List Word} (h : 2 ≤ l.length) :
    ∃ a b rest, l = a :: b :: rest :=
  match l, h with
  | _ :: _ :: rest, _ => ⟨_, _, rest, rfl⟩

theorem toyStep_underflow {prog : List (BitVec 8)} {σ : ToyState}
    (h1 : σ.halted = false) (h2 : σ.gas ≠ 0)
    (hop1 : prog.getD σ.pc 0 ≠ 1) (hop2 : prog.getD σ.pc 0 = 2)
    (hstack : σ.stack.length < 2) :
    toyStep prog σ = { σ with halted := true } := by
  have hop1' : ¬ prog[σ.pc]?.getD 0#8 = 1#8 := hop1
  have hop2' : prog[σ.pc]?.getD 0#8 = 2#8 := hop2
  match hst : σ.stack, hstack with
  | [], _ => simp [toyStep, h1, h2, hop1', hop2', hst]
  | [a], _ => simp [toyStep, h1, h2, hop1', hop2', hst]

/-- A step out of a running state either halts keeping its gas, or stays
    running having consumed exactly one gas.  The disjunction is the gas
    variant in kit form. -/
theorem toyStep_gas_split (prog : List (BitVec 8)) (σ : ToyState) :
    (toyStep prog σ).gas ≤ σ.gas ∧
    ((toyStep prog σ).halted = false → σ.halted = false ∧ σ.gas ≠ 0 ∧
      (toyStep prog σ).gas + 1 = σ.gas) := by
  by_cases h1 : σ.halted
  · rw [toyStep_halted h1]
    exact ⟨Nat.le_refl _, fun hr => absurd h1 (by simp [hr])⟩
  · replace h1 : σ.halted = false := by simpa using h1
    by_cases h2 : σ.gas = 0
    · rw [toyStep_oog h1 h2]
      exact ⟨Nat.le_refl _, fun hr => by simp at hr⟩
    · by_cases hop : prog.getD σ.pc 0 = 1
      · rw [toyStep_push h1 h2 hop]
        exact ⟨by simp only []; omega, fun _ => ⟨h1, h2, by simp only []; omega⟩⟩
      · by_cases hop2 : prog.getD σ.pc 0 = 2
        · by_cases hlen : 2 ≤ σ.stack.length
          · obtain ⟨a, b, rest, hst⟩ := exists_two_cons' hlen
            rw [toyStep_add h1 h2 hop hop2 hst]
            exact ⟨by simp only []; omega,
              fun _ => ⟨h1, h2, by simp only []; omega⟩⟩
          · rw [toyStep_underflow h1 h2 hop hop2 (by omega)]
            exact ⟨Nat.le_refl _, fun hr => by simp at hr⟩
        · rw [toyStep_stop h1 h2 hop hop2]
          exact ⟨by simp only []; omega, fun hr => by simp at hr⟩

/-- Gas is non-increasing along the trace. -/
theorem toyRun_gas_le {prog : List (BitVec 8)} (gas₀ : Nat) :
    ∀ i, (toyRun prog (ToyState.init gas₀) i).gas ≤ gas₀ := by
  intro i
  induction i with
  | zero => exact Nat.le_refl _
  | succ i ih =>
      exact Nat.le_trans
        (toyStep_gas_split prog (toyRun prog (ToyState.init gas₀) i)).1 ih

/-- **The gas variant**: while running, the trace has consumed exactly
    one gas per step.  This is what turns the gas-derived static fuel cap
    into a proof that the loop exits: at `i = cap > gas₀` the state
    cannot still be running. -/
theorem toyRun_gas {prog : List (BitVec 8)} (gas₀ : Nat) :
    ∀ i, (toyRun prog (ToyState.init gas₀) i).halted = false →
      (toyRun prog (ToyState.init gas₀) i).gas + i = gas₀ := by
  intro i
  induction i with
  | zero => intro _; exact Nat.add_zero _
  | succ i ih =>
      intro hrun
      obtain ⟨-, hsplit⟩ :=
        toyStep_gas_split prog (toyRun prog (ToyState.init gas₀) i)
      obtain ⟨hσrun, -, hgas1⟩ := hsplit hrun
      have := ih hσrun
      show (toyStep prog (toyRun prog (ToyState.init gas₀) i)).gas + (i + 1)
        = gas₀
      omega

/-- Per-state safety of a toy program: the pilot's handlers carry no
    runtime guards (the real dispatcher's under/overflow and pc guards
    are separate loop exits, bead .49), so the spec trace must stay in
    bounds.  A running state's next opcode is in bounds; PUSH needs its
    immediate in bounds and stack room; ADD needs two operands. -/
def ToyState.ok (prog : List (BitVec 8)) (σ : ToyState) : Prop :=
  σ.stack.length ≤ 8 ∧ σ.pc ≤ prog.length ∧
  (σ.halted = false →
    σ.pc < prog.length ∧
    (prog.getD σ.pc 0 = 1 → σ.pc + 1 < prog.length ∧ σ.stack.length < 8) ∧
    (prog.getD σ.pc 0 = 2 → 2 ≤ σ.stack.length))

-- ============================================================================
-- The machine encoding
-- ============================================================================

/-- Code region base (legacy valid-memory zone). -/
def toyCodeBase : Word := 0x10000

/-- Stack arena base (legacy valid-memory zone), 64 bytes = 8 slots. -/
def toyStackBase : Word := 0x20000

def toyRegion (prog : List (BitVec 8)) : Region := ⟨toyCodeBase, prog⟩

def toyRw : RwRegion := ⟨toyStackBase, 64⟩

/-- The stack's byte image: top-first, contiguous, little-endian dwords. -/
def stackFlat (st : List Word) : List (BitVec 8) := st.flatMap dwordBytes

@[simp] theorem stackFlat_nil : stackFlat [] = [] := rfl

@[simp] theorem stackFlat_cons (v : Word) (st : List Word) :
    stackFlat (v :: st) = dwordBytes v ++ stackFlat st := rfl

theorem length_stackFlat (st : List Word) :
    (stackFlat st).length = 8 * st.length := by
  induction st with
  | nil => rfl
  | cons v st ih =>
      simp only [stackFlat_cons, List.length_append, length_dwordBytes,
        List.length_cons, ih]
      omega

/-- The window dword at byte offset `k` (what an in-window `LD` reads). -/
def wsDword (ws : List (BitVec 8)) (k : Nat) : Word :=
  packBytes ((ws.drop k).take 8)

/-- The machine encoding of a toy state:
    - `x10` = code pointer (pc as an absolute address),
    - `x12` = stack top pointer (grow-down; empty stack = arena end),
    - `x29` = gas, `x30` = halt flag,
    - the rw window is free space followed by the stack's byte image. -/
def encodes (σ : ToyState) (rf : RegFile)
    (ws : List (BitVec 8)) : Prop :=
  rf.get .x10 = toyCodeBase + BitVec.ofNat 64 σ.pc
  ∧ rf.get .x12 = toyStackBase + BitVec.ofNat 64 (64 - 8 * σ.stack.length)
  ∧ rf.get .x29 = BitVec.ofNat 64 σ.gas
  ∧ rf.get .x30 = (if σ.halted then 1 else 0)
  ∧ ∃ junk : List (BitVec 8), junk.length = 64 - 8 * σ.stack.length
      ∧ ws = junk ++ stackFlat σ.stack

theorem encodes_ws_length {σ : ToyState}
    {rf : RegFile} {ws : List (BitVec 8)} (h : encodes σ rf ws)
    (hlen : σ.stack.length ≤ 8) : ws.length = 64 := by
  obtain ⟨-, -, -, -, junk, hj, rfl⟩ := h
  rw [List.length_append, hj, length_stackFlat]
  omega

-- ============================================================================
-- Byte-window algebra for the grow-down stack
-- ============================================================================

/-- A splice that ends exactly at the list's end is take-and-append. -/
theorem setBytes_tail (xs p : List (BitVec 8)) (k : Nat)
    (h : k + p.length = xs.length) :
    setBytes xs k p = xs.take k ++ p := by
  have h1 : (setBytes xs k p).take k = xs.take k :=
    setBytes_take_of_ge p xs k k (Nat.le_refl k)
  have h2 : ((setBytes xs k p).drop k).take p.length = p :=
    setBytes_slot xs p k (by omega)
  have h3 : (setBytes xs k p).length = xs.length := length_setBytes ..
  have h4 : (setBytes xs k p).drop k = p := by
    conv_lhs => rw [← List.take_of_length_le
      (show ((setBytes xs k p).drop k).length ≤ p.length from by
        rw [List.length_drop, h3]; omega)]
    exact h2
  calc setBytes xs k p
      = (setBytes xs k p).take k ++ (setBytes xs k p).drop k :=
        (List.take_append_drop ..).symm
    _ = xs.take k ++ p := by rw [h1, h4]

/-- Dropping an exact prefix length (variable-index form, so rewriting
    never touches literal `8`s elsewhere in the goal). -/
theorem drop_append_len (xs ys : List (BitVec 8)) (k : Nat)
    (h : xs.length = k) : (xs ++ ys).drop k = ys := by
  rw [← h, List.drop_left]

/-- PUSH's store: splicing a fresh dword at the last free slot turns
    `junk ++ stack` into `junk' ++ (v :: stack)`. -/
theorem push_ws_update (junk : List (BitVec 8)) (st : List Word) (v : Word)
    (k : Nat)
    (hj : junk.length = 64 - 8 * st.length) (hlen : st.length < 8)
    (hk : k = 64 - 8 * st.length - 8) :
    setBytes (junk ++ stackFlat st) k (dwordBytes v)
      = junk.take (64 - 8 * (st.length + 1)) ++ stackFlat (v :: st) := by
  rw [setBytes_append_left _ _ _ _
      (by rw [length_dwordBytes, hj]; omega),
    setBytes_tail _ _ _ (by rw [length_dwordBytes, hj]; omega),
    stackFlat_cons, List.append_assoc,
    show k = 64 - 8 * (st.length + 1) from by omega]

/-- ADD's store: overwriting the second-from-top slot after popping turns
    `junk ++ (a :: b :: rest)` into `(junk ++ a-bytes) ++ ((a+b) :: rest)`. -/
theorem add_ws_update (junk : List (BitVec 8)) (a b : Word)
    (rest : List Word) (k : Nat) (hk : k = junk.length + 8) :
    setBytes (junk ++ stackFlat (a :: b :: rest)) k (dwordBytes (a + b))
      = (junk ++ dwordBytes a) ++ stackFlat ((a + b) :: rest) := by
  rw [stackFlat_cons, stackFlat_cons, stackFlat_cons,
    setBytes_append_right _ _ _ _ (by omega),
    show k - junk.length = 8 from by omega,
    setBytes_append_right _ _ _ _
      (by rw [length_dwordBytes]),
    show (8 : Nat) - (dwordBytes a).length = 0 from by
      rw [length_dwordBytes],
    setBytes_dword_at0, ← List.append_assoc]

/-- Reading the top-of-stack dword. -/
theorem stack_read_top (junk tail : List (BitVec 8)) (a : Word)
    (k : Nat) (hk : junk.length = k) :
    wsDword (junk ++ (dwordBytes a ++ tail)) k = a := by
  unfold wsDword
  rw [drop_append_len _ _ _ hk, take8_dword_append, packBytes_dwordBytes]

/-- Reading the second-from-top dword. -/
theorem stack_read_snd (junk tail : List (BitVec 8)) (a b : Word)
    (k : Nat) (hk : junk.length + 8 = k) :
    wsDword (junk ++ (dwordBytes a ++ (dwordBytes b ++ tail))) k = b := by
  unfold wsDword
  rw [← List.append_assoc, drop_append_len _ _ _
      (by rw [List.length_append, length_dwordBytes]; omega),
    take8_dword_append, packBytes_dwordBytes]

-- ============================================================================
-- Engine-step helpers (loads routed explicitly)
-- ============================================================================

/-- An `LBU` that misses the writable window reads the ro region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd
          ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- An `LD` inside the writable window reads the window dword. -/
theorem execInstrRF_ld_rw (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs)
      = (rf.set rd
          (wsDword ws ((rf.get rs1 + signExtend12 ofs) - rwBase).toNat), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_pos h]
  rfl

/-- A byte-comparison bridge: the zero-extended fetched opcode equals a
    small literal iff the opcode byte does. -/
theorem zeroExtend_byte_eq_iff {b : BitVec 8} {n : Nat} (hn : n < 256) :
    b.zeroExtend 64 = BitVec.ofNat 64 n ↔ b = BitVec.ofNat 8 n := by
  have hb := b.isLt
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, toNat_zeroExtend_byte,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `signExtend12` constants, in `simp only`-able form. -/
theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
theorem se12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
theorem se12_two : signExtend12 (2 : BitVec 12) = (2 : Word) := by decide
theorem se12_eight : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
theorem se12_neg_one : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by
  decide
theorem se12_neg_eight : signExtend12 (-8 : BitVec 12) = (-8 : Word) := by
  decide

/-- Negative-offset address arithmetic, in `simp only`-able form. -/
theorem add_neg_eight (x : Word) : x + (-8 : Word) = x - 8 := by bv_omega

/-- `+ 0` collapse at the `Word` OfNat literal (the shape `se12_zero`
    leaves behind). -/
theorem word_add_zero (x : Word) : x + (0 : Word) = x := by bv_omega

theorem add_neg_one (x : Word) : x + (-1 : Word) = x - 1 := by bv_omega

-- ============================================================================
-- The three handlers: real `Fn`s with snapshot-parameterized contracts
-- ============================================================================

/-- Call-site obligation of the PUSH handler: `x10`/`x12` shaped as a
    code pointer and an in-arena stack pointer, immediate in bounds,
    stack room for one more slot. -/
def pushPre (prog : List (BitVec 8)) : Reach :=
  fun rf _ _ =>
    ∃ pcN len : Nat,
      rf.get .x10 = toyCodeBase + BitVec.ofNat 64 pcN
      ∧ rf.get .x12 = toyStackBase + BitVec.ofNat 64 (64 - 8 * len)
      ∧ pcN + 2 ≤ prog.length ∧ prog.length ≤ 4096 ∧ len < 8

/-- Snapshot-parameterized guarantee of the PUSH handler: exit registers
    and window are *functions of the entry state* — the shape a fixed
    `FnHandle.post` cannot express. -/
def pushPost (prog : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf.get .x10 = rf₀.get .x10 + 2
    ∧ rf.get .x12 = rf₀.get .x12 - 8
    ∧ rf.get .x29 = rf₀.get .x29
    ∧ rf.get .x30 = rf₀.get .x30
    ∧ ws = setBytes ws₀ ((rf₀.get .x12 - 8) - toyStackBase).toNat
        (dwordBytes
          (((toyRegion prog).byteAt (rf₀.get .x10 + 1)).zeroExtend 64))
    ∧ A = A₀

/-- PUSH imm8: fetch the immediate, store it at the new top, move the
    top pointer down, advance pc past opcode+immediate. -/
def pushFnBase (prog : List (BitVec 8)) : Fn where
  name := "hpush"
  region := toyRegion prog
  rw := toyRw
  pre := pushPre prog
  post := fun _ _ _ => True
  body := .block "push"
    [.LBU .x6 .x10 1, .SD .x12 .x6 (-8), .ADDI .x12 .x12 (-8),
     .ADDI .x10 .x10 2]

/-- Call-site obligation of the ADD handler: two operands on the stack. -/
def addPre : Reach :=
  fun rf _ _ =>
    ∃ len : Nat,
      rf.get .x12 = toyStackBase + BitVec.ofNat 64 (64 - 8 * len)
      ∧ 2 ≤ len ∧ len ≤ 8

/-- Snapshot-parameterized guarantee of the ADD handler. -/
def addPost : RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf.get .x10 = rf₀.get .x10 + 1
    ∧ rf.get .x12 = rf₀.get .x12 + 8
    ∧ rf.get .x29 = rf₀.get .x29
    ∧ rf.get .x30 = rf₀.get .x30
    ∧ ws = setBytes ws₀ (((rf₀.get .x12 + 8) - toyStackBase).toNat)
        (dwordBytes
          (wsDword ws₀ ((rf₀.get .x12 - toyStackBase).toNat)
            + wsDword ws₀ (((rf₀.get .x12 + 8) - toyStackBase).toNat)))
    ∧ A = A₀

/-- ADD: pop two, push the sum, advance pc by one. -/
def addFnBase (prog : List (BitVec 8)) : Fn where
  name := "hadd"
  region := toyRegion prog
  rw := toyRw
  pre := addPre
  post := fun _ _ _ => True
  body := .block "add"
    [.LD .x6 .x12 0, .LD .x7 .x12 8, .ADD .x6 .x6 .x7,
     .ADDI .x12 .x12 8, .SD .x12 .x6 0, .ADDI .x10 .x10 1]

/-- Snapshot-parameterized guarantee of the STOP handler: set the halt
    flag, touch nothing else. -/
def stopPost : RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf.get .x10 = rf₀.get .x10
    ∧ rf.get .x12 = rf₀.get .x12
    ∧ rf.get .x29 = rf₀.get .x29
    ∧ rf.get .x30 = 1
    ∧ ws = ws₀
    ∧ A = A₀

/-- STOP (also the invalid-opcode sink): raise the halt flag. -/
def stopFnBase (prog : List (BitVec 8)) : Fn where
  name := "hstop"
  region := toyRegion prog
  rw := toyRw
  pre := fun _ _ _ => True
  post := fun _ _ _ => True
  body := .block "stop" [.LI .x30 1]

-- ============================================================================
-- Handler correctness (the snapshot-parameterized spec families)
-- ============================================================================

theorem pushFn_specS (prog : List (BitVec 8))
    (hwf : (toyRegion prog).wf) :
    (pushFnBase prog).SpecS 0x2000 (pushPost prog) := by
  intro rf₀ ws₀ A₀ hpre
  obtain ⟨pcN, len, hx10, hx12, hpc2, hplen, hlen8⟩ := hpre
  have hnorw : ws₀.length = 64 → ¬ inRw toyStackBase ws₀
      (rf₀.get .x10 + signExtend12 (1 : BitVec 12)) 1 := by
    intro hws64
    unfold inRw
    intro hcontra
    rw [hx10, hws64,
      show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
      at hcontra
    simp only [toyCodeBase, toyStackBase] at hcontra
    bv_omega
  vcgen
  case region => exact ⟨hwf, show toyRw.wf by decide⟩
  case hpush.push.mem =>
    rintro rf ws A hws ⟨h1, h2, -⟩
    rw [h2] at hws
    have hws64 : ws₀.length = 64 := hws
    rw [h1, h2]
    dsimp only [pushFnBase, toyRw, toyRegion, blockVCs, loadSem, storeSem,
      Region.loadOk]
    rw [if_neg (hnorw hws64), execInstrRF_lbu_ro _ _ _ _ _ _ _ (hnorw hws64)]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
      se12_eight, se12_neg_eight, BitVec.add_zero, word_add_zero, add_neg_eight]
    simp only [toyCodeBase, toyStackBase] at hx10 hx12 ⊢
    have hidxL : ((rf₀.get .x10 + 1) - 0x10000 : Word).toNat = pcN + 1 := by
      rw [hx10]; bv_omega
    have hidxS : ((rf₀.get .x12 - 8) - 0x20000 : Word).toNat
        = 64 - 8 * len - 8 := by
      rw [hx12]; bv_omega
    and_intros
    · exact one_dvd _
    · rw [hidxL]; omega
    · unfold inRw; rw [hidxS, hws64]; omega
    · rw [hidxS]; omega
    · trivial
    · trivial
    · trivial
  case hpush.post =>
    rintro rf' ws' A' ⟨rfE, wsE, hws, ⟨h1, h2, h3⟩, rfl, rfl⟩
    rw [h2] at hws
    have hws64 : ws₀.length = 64 := hws
    rw [h1, h2, h3]
    dsimp only [pushFnBase, toyRw, toyRegion, pushPost]
    rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ (hnorw hws64)]
    dsimp only
    rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _
      (((rf₀.get .x12 - 8) - toyStackBase).toNat)
      (by rw [RegFile.get_set_ne _ _ _ _ (by decide),
          show signExtend12 (-8 : BitVec 12) = (-8 : Word) from by decide]
          bv_omega)]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
      se12_eight, se12_neg_eight, BitVec.add_zero, word_add_zero, add_neg_eight, and_true, true_and]
    try bv_omega

theorem addFn_specS (prog : List (BitVec 8))
    (hwf : (toyRegion prog).wf) :
    (addFnBase prog).SpecS 0x2100 addPost := by
  intro rf₀ ws₀ A₀ hpre
  obtain ⟨len, hx12, hlen2, hlen8⟩ := hpre
  have hrw0 : ws₀.length = 64 → inRw toyStackBase ws₀
      (rf₀.get .x12 + signExtend12 (0 : BitVec 12)) 8 := by
    intro hws64
    unfold inRw
    rw [hx12, hws64,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    simp only [toyStackBase]
    bv_omega
  vcgen
  case region => exact ⟨hwf, show toyRw.wf by decide⟩
  case hadd.add.mem =>
    rintro rf ws A hws ⟨h1, h2, -⟩
    rw [h2] at hws
    have hws64 : ws₀.length = 64 := hws
    rw [h1, h2]
    have hrw8 : inRw toyStackBase ws₀
        (rf₀.get .x12 + signExtend12 (8 : BitVec 12)) 8 := by
      unfold inRw
      rw [hx12, hws64,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      simp only [toyStackBase]
      bv_omega
    dsimp only [addFnBase, toyRw, toyRegion, blockVCs, loadSem, storeSem,
      Region.loadOk]
    rw [if_pos (hrw0 hws64), execInstrRF_ld_rw _ _ _ _ _ _ _ (hrw0 hws64)]
    dsimp only
    have hrw8' : inRw toyStackBase ws₀
        ((rf₀.set .x6 (wsDword ws₀
            ((rf₀.get .x12 + signExtend12 (0 : BitVec 12))
              - toyStackBase).toNat)).get .x12
          + signExtend12 (8 : BitVec 12)) 8 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      exact hrw8
    rw [if_pos hrw8', execInstrRF_ld_rw _ _ _ _ _ _ _ hrw8']
    dsimp only [execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
      se12_eight, se12_neg_eight, BitVec.add_zero, word_add_zero]
    simp only [toyStackBase] at hx12 ⊢
    have hidx0 : ((rf₀.get .x12) - 0x20000 : Word).toNat = 64 - 8 * len := by
      rw [hx12]; bv_omega
    have hidx8 : ((rf₀.get .x12 + 8) - 0x20000 : Word).toNat
        = 64 - 8 * len + 8 := by
      rw [hx12]; bv_omega
    and_intros
    · rw [hidx0]; omega
    · rw [hidx0, hws64]; omega
    · rw [hidx8]; omega
    · rw [hidx8, hws64]; omega
    · trivial
    · trivial
    · unfold inRw; rw [hidx8, hws64]; omega
    · rw [hidx8]; omega
    · trivial
    · trivial
  case hadd.post =>
    rintro rf' ws' A' ⟨rfE, wsE, hws, ⟨h1, h2, h3⟩, rfl, rfl⟩
    rw [h2] at hws
    have hws64 : ws₀.length = 64 := hws
    rw [h1, h2, h3]
    dsimp only [addFnBase, toyRw, toyRegion, addPost]
    rw [execBlock_cons, execInstrRF_ld_rw _ _ _ _ _ _ _ (hrw0 hws64)]
    dsimp only
    have hrw8' : inRw toyStackBase ws₀
        ((rf₀.set .x6 (wsDword ws₀
            ((rf₀.get .x12 + signExtend12 (0 : BitVec 12))
              - toyStackBase).toNat)).get .x12
          + signExtend12 (8 : BitVec 12)) 8 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      unfold inRw
      rw [hx12, hws64, se12_eight]
      simp only [toyStackBase]
      bv_omega
    rw [execBlock_cons, execInstrRF_ld_rw _ _ _ _ _ _ _ hrw8']
    dsimp only
    rw [execBlock_cons]
    dsimp only [execInstrRF, aluSem]
    rw [execBlock_cons]
    dsimp only [execInstrRF, aluSem]
    rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _
      (((rf₀.get .x12 + 8) - toyStackBase).toNat)
      (by
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
      se12_eight, se12_neg_eight, BitVec.add_zero, word_add_zero]
        try bv_omega)]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
      se12_eight, se12_neg_eight, BitVec.add_zero, word_add_zero, and_true, true_and]
    try bv_omega

theorem stopFn_specS (prog : List (BitVec 8))
    (hwf : (toyRegion prog).wf) :
    (stopFnBase prog).SpecS 0x2200 stopPost := by
  intro rf₀ ws₀ A₀ _hpre
  vcgen
  case region => exact ⟨hwf, show toyRw.wf by decide⟩
  case hstop.post =>
    rintro rf' ws' A' ⟨rfE, wsE, hws, ⟨h1, h2, h3⟩, rfl, rfl⟩
    rw [h1, h2, h3]
    dsimp only [stopFnBase, toyRw, toyRegion, stopPost]
    simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
      reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
      se12_eight, se12_neg_eight, BitVec.add_zero, word_add_zero, and_true, true_and]
    try bv_omega

-- ============================================================================
-- The handles
-- ============================================================================

def pushHandle (prog : List (BitVec 8)) (hwf : (toyRegion prog).wf) :
    FnHandleS :=
  (pushFnBase prog).toHandleS 0x2000 (pushPost prog)
    (pushFn_specS prog hwf) (by change 4 * (4 + 1) ≤ 2 ^ 64; decide)

def addHandle (prog : List (BitVec 8)) (hwf : (toyRegion prog).wf) :
    FnHandleS :=
  (addFnBase prog).toHandleS 0x2100 addPost
    (addFn_specS prog hwf) (by change 4 * (6 + 1) ≤ 2 ^ 64; decide)

def stopHandle (prog : List (BitVec 8)) (hwf : (toyRegion prog).wf) :
    FnHandleS :=
  (stopFnBase prog).toHandleS 0x2200 stopPost
    (stopFn_specS prog hwf) (by change 4 * (1 + 1) ≤ 2 ^ 64; decide)

-- ============================================================================
-- The interpreter loop
-- ============================================================================

/-- The fetch-charge block: charge one gas, fetch the opcode, load the
    comparison constants. -/
def fetchInstrs : List Instr :=
  [.ADDI .x29 .x29 (-1), .LBU .x5 .x10 0, .LI .x6 1, .LI .x7 2]

/-- The handler-address select cascade (the toy's `opcode_handlers`
    lookup; the real loop's table load is ordinary ro-region machinery,
    design §3.6.3). -/
def selStmt : Stmt :=
  .ite "sel1" (.beq .x5 .x6)
    (.block "goPush" [.LI .x28 0x2000])
    (.ite "sel2" (.beq .x5 .x7)
      (.block "goAdd" [.LI .x28 0x2100])
      (.block "goStop" [.LI .x28 0x2200]))

/-- The loop invariant (entry-snapshot-parameterized): the machine
    encodes exactly the `i`-th state of the spec trace whose initial gas
    is read from the *snapshot's* gas register — the per-execution
    constant reaches the invariant only through the `whileS` snapshot. -/
def interpInv (prog : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → Nat →
      RegFile → List (BitVec 8) → Assertion → Prop :=
  fun rf₀ _ _ i rf ws _ =>
    encodes (toyRun prog (ToyState.init (rf₀.get .x29).toNat) i) rf ws

/-- The interpreter: while running, charge, fetch, select, dispatch.
    Fuel is the static cap `cap` (gas-derived: any `cap > gas₀` works). -/
def interpFn (prog : List (BitVec 8)) (hwf : (toyRegion prog).wf)
    (gas₀ cap : Nat) : Fn where
  name := "interp"
  region := toyRegion prog
  rw := toyRw
  pre := fun rf ws _ =>
    rf.get .x10 = toyCodeBase
    ∧ rf.get .x12 = toyStackBase + 64
    ∧ rf.get .x29 = BitVec.ofNat 64 gas₀
    ∧ rf.get .x30 = 0
    ∧ ws.length = 64
  post := fun rf ws _ =>
    encodes (toyRun prog (ToyState.init gas₀) cap) rf ws
  body :=
    .«whileS» "run" (.beq .x30 .x0) cap (interpInv prog)
      (.ite "fuel" (.beq .x29 .x0)
        (.block "oog" [.LI .x30 1])
        (.block "fetch" fetchInstrs ;;;
         selStmt ;;;
         .callRegS "disp" .x28
           [pushHandle prog hwf, addHandle prog hwf, stopHandle prog hwf]))

/-- The ambient code requirement: loop code plus the three handlers. -/
def interpCr (prog : List (BitVec 8)) (hwf : (toyRegion prog).wf)
    (gas₀ cap : Nat) : CodeReq :=
  (((CodeReq.ofProg 0x1000
      ((interpFn prog hwf gas₀ cap).body.flatten 0x1000)).union
    (pushHandle prog hwf).code).union
    (addHandle prog hwf).code).union
    (stopHandle prog hwf).code

-- ============================================================================
-- The simulation theorem
-- ============================================================================

/-- The fetch-charge block, fully executed: charge one gas into `x29`,
    fetch the opcode byte at `pc` into `x5`, load the selector constants. -/
theorem exec_fetch (prog : List (BitVec 8)) (rfE : RegFile)
    (wsE : List (BitVec 8)) (pcN : Nat) (hws : wsE.length = 64)
    (hx10 : rfE.get .x10 = toyCodeBase + BitVec.ofNat 64 pcN)
    (hpc : pcN < prog.length) (hplen : prog.length ≤ 4096) :
    execBlock (toyRegion prog) toyStackBase rfE wsE fetchInstrs
      = ((((rfE.set .x29 (rfE.get .x29 - 1)).set .x5
            ((prog.getD pcN 0).zeroExtend 64)).set .x6 1).set .x7 2, wsE) := by
  have hnorw : ¬ inRw toyStackBase wsE
      ((rfE.set .x29 (rfE.get .x29 + signExtend12 (-1 : BitVec 12))).get .x10
        + signExtend12 (0 : BitVec 12)) 1 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide)]
    unfold inRw
    rw [hx10, hws, se12_zero]
    simp only [toyCodeBase, toyStackBase]
    bv_omega
  dsimp only [fetchInstrs]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hnorw]
  simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
    reduceCtorEq, not_false_eq_true, se12_zero, se12_one, se12_two,
    se12_eight, se12_neg_eight, se12_neg_one, BitVec.add_zero,
    word_add_zero, add_neg_one]
  rw [hx10]
  dsimp only [toyRegion, Region.byteAt]
  rw [show ((toyCodeBase + BitVec.ofNat 64 pcN) - toyCodeBase).toNat = pcN
    from by simp only [toyCodeBase]; bv_omega]

/-- A handler-select block, fully executed. -/
theorem exec_li28 (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (c : Word) :
    execBlock ro rwBase rf ws [.LI .x28 c] = (rf.set .x28 c, ws) := rfl

/-- The out-of-gas halt block, fully executed. -/
theorem exec_li30 (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (c : Word) :
    execBlock ro rwBase rf ws [.LI .x30 c] = (rf.set .x30 c, ws) := rfl

/-- The fetched-opcode compare against selector constant 1. -/
theorem opbyte_one_iff (b : BitVec 8) :
    b.zeroExtend 64 = (1 : Word) ↔ b = 1 :=
  zeroExtend_byte_eq_iff (n := 1) (by omega)

/-- The fetched-opcode compare against selector constant 2. -/
theorem opbyte_two_iff (b : BitVec 8) :
    b.zeroExtend 64 = (2 : Word) ↔ b = 2 :=
  zeroExtend_byte_eq_iff (n := 2) (by omega)

/-- **The pilot's simulation theorem**: the interpreter loop, run to its
    (gas-derived, statically capped) exit, leaves the machine encoding
    exactly `toyRun prog (ToyState.init gas₀) cap` — the deterministic
    spec-side execution, frozen at its halt point.

    Hypotheses: a well-formed code region, a code size bound, the
    gas-derived cap (`gas₀ < cap`: any such cap works — the static-cap
    idiom), and spec-side trace safety (`hsafe`, standing in for the
    real dispatcher's runtime guards). -/
theorem interpFn_spec (prog : List (BitVec 8))
    (hwf : (toyRegion prog).wf)
    (hplen : prog.length ≤ 4096)
    (gas₀ cap : Nat) (hgas : gas₀ < cap) (hcap : cap ≤ 2 ^ 32)
    (hsafe : ∀ i, ToyState.ok prog (toyRun prog (ToyState.init gas₀) i)) :
    (interpFn prog hwf gas₀ cap).SpecR 0x1000 (interpCr prog hwf gas₀ cap) := by
  vcgen
  case region => exact ⟨hwf, show toyRw.wf by decide⟩
  case code =>
    intro a i h
    simp only [interpCr, CodeReq.union, h]
  case callees =>
    have hcodePush : ∀ a i, (pushHandle prog hwf).code a = some i →
        interpCr prog hwf gas₀ cap a = some i := by
      intro a i h
      obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
      have hk5 : kk < 5 := hk
      have hP : CodeReq.ofProg 0x1000
          ((interpFn prog hwf gas₀ cap).body.flatten 0x1000)
          ((0x2000 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk17 : k' < 17 := hk'
        bv_omega
      simp only [interpCr, CodeReq.union, hP, h]
    have hcodeAdd : ∀ a i, (addHandle prog hwf).code a = some i →
        interpCr prog hwf gas₀ cap a = some i := by
      intro a i h
      obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
      have hk7 : kk < 7 := hk
      have hP : CodeReq.ofProg 0x1000
          ((interpFn prog hwf gas₀ cap).body.flatten 0x1000)
          ((0x2100 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk17 : k' < 17 := hk'
        bv_omega
      have hPu : (pushHandle prog hwf).code
          ((0x2100 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
        show CodeReq.ofProg 0x2000 ((pushFnBase prog).programRet 0x2000) _
          = none
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk5 : k' < 5 := hk'
        bv_omega
      simp only [interpCr, CodeReq.union, hP, hPu, h]
    have hcodeStop : ∀ a i, (stopHandle prog hwf).code a = some i →
        interpCr prog hwf gas₀ cap a = some i := by
      intro a i h
      obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
      have hk2 : kk < 2 := hk
      have hP : CodeReq.ofProg 0x1000
          ((interpFn prog hwf gas₀ cap).body.flatten 0x1000)
          ((0x2200 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk17 : k' < 17 := hk'
        bv_omega
      have hPu : (pushHandle prog hwf).code
          ((0x2200 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
        show CodeReq.ofProg 0x2000 ((pushFnBase prog).programRet 0x2000) _
          = none
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk5 : k' < 5 := hk'
        bv_omega
      have hAu : (addHandle prog hwf).code
          ((0x2200 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
        show CodeReq.ofProg 0x2100 ((addFnBase prog).programRet 0x2100) _
          = none
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk7 : k' < 7 := hk'
        bv_omega
      simp only [interpCr, CodeReq.union, hP, hPu, hAu, h]
    refine ⟨trivial, trivial, ⟨trivial, trivial, trivial⟩, ?_⟩
    intro h hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact ⟨hcodePush, rfl, rfl⟩
    · exact ⟨hcodeAdd, rfl, rfl⟩
    · exact ⟨hcodeStop, rfl, rfl⟩
  case calls =>
    refine ⟨trivial, trivial, ⟨trivial, trivial, trivial⟩, ?_, ?_⟩
    · decide
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact show ((0x2000 : Word) &&& ~~~(1 : Word)) = 0x2000 by decide
      · exact show ((0x2100 : Word) &&& ~~~(1 : Word)) = 0x2100 by decide
      · exact show ((0x2200 : Word) &&& ~~~(1 : Word)) = 0x2200 by decide
  case interp.run.inv_init =>
    rintro rf ws A ⟨hx10, hx12, hx29, hx30, hws64⟩
    dsimp only [interpInv, toyRun, ToyState.init, encodes, List.length_nil,
      stackFlat_nil]
    refine ⟨?_, ?_, ?_, hx30, ws, ?_, (List.append_nil ws).symm⟩
    · rw [hx10]
      simp only [toyCodeBase]
      bv_omega
    · rw [hx12]
      simp only [toyStackBase]
      bv_omega
    · rw [hx29, toNat_ofNat_lt (show gas₀ < 2 ^ 64 from by omega)]
    · rw [hws64]
  case interp.run.inv_step =>
    rintro rf₀ ws₀ A₀ ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩ i hi rf' ws' A'
      hsp
    have hg : (rf₀.get .x29).toNat = gas₀ := by
      rw [hx29₀]; exact toNat_ofNat_lt (by omega)
    dsimp only [interpInv] at hsp ⊢
    rw [hg] at hsp ⊢
    rcases hsp with
        ⟨rfE, wsE, hlenE, ⟨⟨hinv, hcond⟩, hfuel⟩, rfl, rfl⟩
      | ⟨rf1, ws1, A₁,
          (⟨rfF, wsF, hlenF,
              ⟨⟨rfE, wsE, hlenE, ⟨⟨hinv, hcond⟩, hnfuel⟩, rfl, rfl⟩, hc1⟩,
              rfl, rfl⟩
          | ⟨rfF, wsF, hlenF,
              ⟨⟨⟨rfE, wsE, hlenE, ⟨⟨hinv, hcond⟩, hnfuel⟩, rfl, rfl⟩,
                hnc1⟩, hc2⟩, rfl, rfl⟩
          | ⟨rfF, wsF, hlenF,
              ⟨⟨⟨rfE, wsE, hlenE, ⟨⟨hinv, hcond⟩, hnfuel⟩, rfl, rfl⟩,
                hnc1⟩, hnc2⟩, rfl, rfl⟩),
          h, hmem, hx28, hpre, hpost⟩
    -- out-of-gas: halt without dispatch
    · obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond hfuel
      rw [RegFile.get_x0] at hcond hfuel
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hgas0 : (toyRun prog (ToyState.init gas₀) i).gas = 0 := by
        have hle := toyRun_gas_le (prog := prog) gas₀ i
        rw [hx29] at hfuel
        bv_omega
      show encodes (toyStep prog (toyRun prog (ToyState.init gas₀) i)) _ _
      rw [toyStep_oog hrun hgas0, exec_li30]
      dsimp only [encodes]
      rw [hrun] at hx30
      refine ⟨?_, ?_, ?_, ?_, junk, hj, hwseq⟩
      · rw [RegFile.get_set_ne _ _ _ _ (by decide)]; exact hx10
      · rw [RegFile.get_set_ne _ _ _ _ (by decide)]; exact hx12
      · rw [RegFile.get_set_ne _ _ _ _ (by decide)]; exact hx29
      · rw [RegFile.get_set_self _ _ _ (by decide)]
        rfl
    -- goPush select branch
    · dsimp only [interpFn, toyRw] at hlenE hc1 hx28 hpost
      obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond hc1 hnfuel
      rw [RegFile.get_x0] at hcond hnfuel
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hok := hsafe i
      have hpclt := (hok.2.2 hrun).1
      have hgasne : (toyRun prog (ToyState.init gas₀) i).gas ≠ 0 := by
        intro h0
        apply hnfuel
        rw [hx29, h0]
        rfl
      rw [exec_fetch prog rfE ws1 _ hlenE hx10 hpclt hplen] at hc1 hx28 hpost
      rw [exec_li28] at hx28 hpost
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true] at hc1 hx28
      have hop := (opbyte_one_iff _).mp hc1
      obtain ⟨hpc1, hlen8⟩ := (hok.2.2 hrun).2.1 hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · -- pushHandle selected: the real transition
        dsimp only [pushHandle, Fn.toHandleS, pushPost] at hpost
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true] at hpost
        obtain ⟨hp10, hp12, hp29, hp30, hpws, -⟩ := hpost
        show encodes (toyStep prog (toyRun prog (ToyState.init gas₀) i)) _ _
        rw [toyStep_push hrun hgasne hop]
        dsimp only [encodes, List.length_cons]
        rw [hrun] at hx30
        have hgle := toyRun_gas_le (prog := prog) gas₀ i
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hp10, hx10]
          simp only [toyCodeBase]
          bv_omega
        · rw [hp12, hx12]
          simp only [toyStackBase]
          bv_omega
        · rw [hp29, hx29]
          bv_omega
        · rw [hp30, hx30]
        · rw [hwseq] at hpws
          rw [show ((rfE.get .x12 - 8) - toyStackBase).toNat
              = 64 - 8 * (toyRun prog (ToyState.init gas₀) i).stack.length - 8
            from by
              rw [hx12]
              simp only [toyStackBase]
              bv_omega] at hpws
          rw [show (toyRegion prog).byteAt (rfE.get .x10 + 1)
              = prog.getD ((toyRun prog (ToyState.init gas₀) i).pc + 1) 0
            from by
              dsimp only [toyRegion, Region.byteAt]
              rw [hx10]
              congr 1
              simp only [toyCodeBase]
              bv_omega] at hpws
          rw [push_ws_update junk _ _ _ hj hlen8 rfl] at hpws
          refine ⟨junk.take
            (64 - 8 * ((toyRun prog (ToyState.init gas₀) i).stack.length + 1)),
            ?_, ?_⟩
          · rw [List.length_take, hj]
            omega
          · exact hpws
      · -- addHandle selected: contradicts the select branch
        exact absurd hx28 (show ¬ ((8192 : Word) = 8448) from by decide)
      · exact absurd hx28 (show ¬ ((8192 : Word) = 8704) from by decide)
    -- goAdd select branch
    · dsimp only [interpFn, toyRw] at hlenE hc2 hnc1 hx28 hpost
      obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond hc2 hnc1 hnfuel
      rw [RegFile.get_x0] at hcond hnfuel
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hok := hsafe i
      have hpclt := (hok.2.2 hrun).1
      have hgasne : (toyRun prog (ToyState.init gas₀) i).gas ≠ 0 := by
        intro h0
        apply hnfuel
        rw [hx29, h0]
        rfl
      rw [exec_fetch prog rfE ws1 _ hlenE hx10 hpclt hplen] at hc2 hnc1 hx28 hpost
      rw [exec_li28] at hx28 hpost
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true] at hc2 hnc1 hx28
      have hop := (opbyte_two_iff _).mp hc2
      have hopne1 : prog.getD (toyRun prog (ToyState.init gas₀) i).pc 0
          ≠ 1 := fun hh => hnc1 ((opbyte_one_iff _).mpr hh)
      have hlen2 := (hok.2.2 hrun).2.2 hop
      obtain ⟨a, b, rest, hst⟩ := exists_two_cons' hlen2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd hx28 (show ¬ ((8448 : Word) = 8192) from by decide)
      · -- addHandle selected: the real transition
        dsimp only [addHandle, Fn.toHandleS, addPost] at hpost
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true] at hpost
        obtain ⟨hp10, hp12, hp29, hp30, hpws, -⟩ := hpost
        show encodes (toyStep prog (toyRun prog (ToyState.init gas₀) i)) _ _
        rw [toyStep_add hrun hgasne hopne1 hop hst]
        dsimp only [encodes, List.length_cons]
        rw [hrun] at hx30
        have hgle := toyRun_gas_le (prog := prog) gas₀ i
        have hlenval : (toyRun prog (ToyState.init gas₀) i).stack.length
            = rest.length + 2 := by
          rw [hst]
          simp
        have hstk8 : (toyRun prog (ToyState.init gas₀) i).stack.length
            ≤ 8 := hok.1
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hp10, hx10]
          simp only [toyCodeBase]
          bv_omega
        · rw [hp12, hx12]
          simp only [toyStackBase]
          bv_omega
        · rw [hp29, hx29]
          bv_omega
        · rw [hp30, hx30]
        · rw [hwseq, hst] at hpws
          rw [show ((rfE.get .x12) - toyStackBase).toNat
              = 64 - 8 * (toyRun prog (ToyState.init gas₀) i).stack.length
            from by
              rw [hx12]
              simp only [toyStackBase]
              bv_omega] at hpws
          rw [show ((rfE.get .x12 + 8) - toyStackBase).toNat
              = 64 - 8 * (toyRun prog (ToyState.init gas₀) i).stack.length
                + 8
            from by
              rw [hx12]
              simp only [toyStackBase]
              bv_omega] at hpws
          rw [show stackFlat (a :: b :: rest)
              = dwordBytes a ++ (dwordBytes b ++ stackFlat rest)
            from rfl] at hpws
          rw [stack_read_top junk _ a _ (by rw [hj]),
            stack_read_snd junk _ a b _ (by rw [hj])] at hpws
          rw [show (dwordBytes a ++ (dwordBytes b ++ stackFlat rest))
              = stackFlat (a :: b :: rest) from rfl] at hpws
          rw [add_ws_update junk a b rest _ (by rw [hj])] at hpws
          refine ⟨junk ++ dwordBytes a, ?_, ?_⟩
          · rw [List.length_append, length_dwordBytes, hj, hlenval]
            omega
          · exact hpws
      · exact absurd hx28 (show ¬ ((8448 : Word) = 8704) from by decide)
    -- goStop select branch
    · dsimp only [interpFn, toyRw] at hlenE hnc1 hnc2 hx28 hpost
      obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond hnc1 hnc2 hnfuel
      rw [RegFile.get_x0] at hcond hnfuel
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hok := hsafe i
      have hpclt := (hok.2.2 hrun).1
      have hgasne : (toyRun prog (ToyState.init gas₀) i).gas ≠ 0 := by
        intro h0
        apply hnfuel
        rw [hx29, h0]
        rfl
      rw [exec_fetch prog rfE ws1 _ hlenE hx10 hpclt hplen] at hnc1 hnc2 hx28 hpost
      rw [exec_li28] at hx28 hpost
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true] at hnc1 hnc2 hx28
      have hopne1 : prog.getD (toyRun prog (ToyState.init gas₀) i).pc 0
          ≠ 1 := fun hh => hnc1 ((opbyte_one_iff _).mpr hh)
      have hopne2 : prog.getD (toyRun prog (ToyState.init gas₀) i).pc 0
          ≠ 2 := fun hh => hnc2 ((opbyte_two_iff _).mpr hh)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact absurd hx28 (show ¬ ((8704 : Word) = 8192) from by decide)
      · exact absurd hx28 (show ¬ ((8704 : Word) = 8448) from by decide)
      · -- stopHandle selected: the real transition
        dsimp only [stopHandle, Fn.toHandleS, stopPost] at hpost
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true] at hpost
        obtain ⟨hp10, hp12, hp29, hp30, hpws, -⟩ := hpost
        show encodes (toyStep prog (toyRun prog (ToyState.init gas₀) i)) _ _
        rw [toyStep_stop hrun hgasne hopne1 hopne2]
        dsimp only [encodes]
        rw [hrun] at hx30
        have hgle := toyRun_gas_le (prog := prog) gas₀ i
        refine ⟨?_, ?_, ?_, ?_, junk, hj, ?_⟩
        · rw [hp10]
          exact hx10
        · rw [hp12]
          exact hx12
        · rw [hp29, hx29]
          bv_omega
        · rw [hp30]
          rfl
        · rw [hpws]
          exact hwseq
  case interp.run.exhausted =>
    rintro rf₀ ws₀ A₀ ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩ rf ws A hinv
    have hg : (rf₀.get .x29).toNat = gas₀ := by
      rw [hx29₀]
      exact toNat_ofNat_lt (by omega)
    dsimp only [interpInv] at hinv
    rw [hg] at hinv
    obtain ⟨-, -, -, hx30, -⟩ := hinv
    intro hcond
    dsimp only [Cond.holds] at hcond
    rw [RegFile.get_x0] at hcond
    by_cases hh : (toyRun prog (ToyState.init gas₀) cap).halted
    · rw [hh] at hx30
      rw [hx30] at hcond
      exact absurd hcond (by decide)
    · replace hh : (toyRun prog (ToyState.init gas₀) cap).halted = false := by
        simpa using hh
      have := toyRun_gas gas₀ cap hh
      omega
  case interp.run.body.fuel.e.fetch.mem =>
    rintro rf ws A hws
      ⟨⟨rf₀, ws₀, A₀, ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩,
        i, hi, hinv, hcond⟩, hnfuel⟩
    have hg : (rf₀.get .x29).toNat = gas₀ := by
      rw [hx29₀]
      exact toNat_ofNat_lt (by omega)
    dsimp only [interpInv] at hinv
    rw [hg] at hinv
    obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
    dsimp only [Cond.holds] at hcond
    rw [RegFile.get_x0] at hcond
    have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
      by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
      · rw [hh] at hx30
        rw [hx30] at hcond
        exact absurd hcond (by decide)
      · simpa using hh
    have hpclt := ((hsafe i).2.2 hrun).1
    have hws64 : ws.length = 64 := hws
    have hnorw : ¬ inRw toyStackBase ws
        ((rf.set .x29 (rf.get .x29 + signExtend12 (-1 : BitVec 12))).get .x10
          + signExtend12 (0 : BitVec 12)) 1 := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide)]
      unfold inRw
      rw [hx10, hws64, se12_zero]
      simp only [toyCodeBase, toyStackBase]
      have hple := (hsafe i).2.1
      bv_omega
    dsimp only [interpFn, toyRw, toyRegion, fetchInstrs, blockVCs, loadSem,
      storeSem, Region.loadOk, execInstrRF, aluSem]
    rw [if_neg hnorw]
    refine ⟨trivial, ⟨one_dvd _, ?_⟩, trivial, trivial, trivial⟩
    rw [RegFile.get_set_ne _ _ _ _ (by decide), hx10, se12_zero]
    simp only [toyCodeBase]
    have hple := (hsafe i).2.1
    bv_omega
  case interp.run.body.fuel.e.disp.pre =>
    rintro rf₁ ws₁ A₁
      (⟨rfF, wsF, hlenF,
          ⟨⟨rfE, wsE, hlenE,
            ⟨⟨rf₀, ws₀, A₀, ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩,
              i, hi, hinv, hcond⟩, hnfuel⟩, rfl, rfl⟩, hc1⟩, rfl, rfl⟩
      | ⟨rfF, wsF, hlenF,
          ⟨⟨⟨rfE, wsE, hlenE,
            ⟨⟨rf₀, ws₀, A₀, ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩,
              i, hi, hinv, hcond⟩, hnfuel⟩, rfl, rfl⟩, hnc1⟩, hc2⟩, rfl, rfl⟩
      | ⟨rfF, wsF, hlenF,
          ⟨⟨⟨rfE, wsE, hlenE,
            ⟨⟨rf₀, ws₀, A₀, ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩,
              i, hi, hinv, hcond⟩, hnfuel⟩, rfl, rfl⟩, hnc1⟩, hnc2⟩, rfl, rfl⟩)
    -- goPush branch
    · dsimp only [interpFn, toyRw] at hlenE hc1 ⊢
      dsimp only [interpInv] at hinv
      rw [show (rf₀.get .x29).toNat = gas₀ from by
        rw [hx29₀]; exact toNat_ofNat_lt (by omega)] at hinv
      obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond hc1
      rw [RegFile.get_x0] at hcond
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hok := hsafe i
      have hpclt := (hok.2.2 hrun).1
      rw [exec_fetch prog rfE ws₁ _ hlenE hx10 hpclt hplen] at hc1 ⊢
      rw [exec_li28]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true] at hc1
      have hop := (opbyte_one_iff _).mp hc1
      obtain ⟨hpc1, hlen8⟩ := (hok.2.2 hrun).2.1 hop
      refine ⟨pushHandle prog hwf, by simp, ?_, ?_⟩
      · simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
          not_false_eq_true]
        rfl
      · dsimp only [pushHandle, Fn.toHandleS, pushFnBase, pushPre]
        refine ⟨(toyRun prog (ToyState.init gas₀) i).pc,
          (toyRun prog (ToyState.init gas₀) i).stack.length,
          ?_, ?_, by omega, hplen, hlen8⟩
        · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
            reduceCtorEq, not_false_eq_true]
          exact hx10
        · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
            reduceCtorEq, not_false_eq_true]
          exact hx12
    -- goAdd branch
    · dsimp only [interpFn, toyRw] at hlenE hc2 ⊢
      dsimp only [interpInv] at hinv
      rw [show (rf₀.get .x29).toNat = gas₀ from by
        rw [hx29₀]; exact toNat_ofNat_lt (by omega)] at hinv
      obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond hc2
      rw [RegFile.get_x0] at hcond
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hok := hsafe i
      have hpclt := (hok.2.2 hrun).1
      rw [exec_fetch prog rfE ws₁ _ hlenE hx10 hpclt hplen] at hc2 ⊢
      rw [exec_li28]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
        reduceCtorEq, not_false_eq_true] at hc2
      have hop := (opbyte_two_iff _).mp hc2
      have hlen2 := (hok.2.2 hrun).2.2 hop
      refine ⟨addHandle prog hwf, by simp, ?_, ?_⟩
      · simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
          not_false_eq_true]
        rfl
      · dsimp only [addHandle, Fn.toHandleS, addFnBase, addPre]
        refine ⟨(toyRun prog (ToyState.init gas₀) i).stack.length,
          ?_, hlen2, hok.1⟩
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true]
        exact hx12
    -- goStop branch
    · dsimp only [interpFn, toyRw] at hlenE ⊢
      dsimp only [interpInv] at hinv
      rw [show (rf₀.get .x29).toNat = gas₀ from by
        rw [hx29₀]; exact toNat_ofNat_lt (by omega)] at hinv
      obtain ⟨hx10, hx12, hx29, hx30, junk, hj, hwseq⟩ := hinv
      dsimp only [Cond.holds] at hcond
      rw [RegFile.get_x0] at hcond
      have hrun : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        by_cases hh : (toyRun prog (ToyState.init gas₀) i).halted
        · rw [hh] at hx30; rw [hx30] at hcond; exact absurd hcond (by decide)
        · simpa using hh
      have hok := hsafe i
      have hpclt := (hok.2.2 hrun).1
      rw [exec_fetch prog rfE ws₁ _ hlenE hx10 hpclt hplen]
      rw [exec_li28]
      refine ⟨stopHandle prog hwf, by simp, ?_, trivial⟩
      simp only [RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rfl
  case interp.post =>
    rintro rf ws A
      ⟨rf₀, ws₀, A₀, ⟨hx10₀, hx12₀, hx29₀, hx30₀, hws₀64⟩,
        ⟨i, hile, hinv⟩, hncond⟩
    have hg : (rf₀.get .x29).toNat = gas₀ := by
      rw [hx29₀]
      exact toNat_ofNat_lt (by omega)
    dsimp only [interpInv] at hinv
    rw [hg] at hinv
    have hhalt : (toyRun prog (ToyState.init gas₀) i).halted = true := by
      by_contra hh
      replace hh : (toyRun prog (ToyState.init gas₀) i).halted = false := by
        simpa using hh
      apply hncond
      dsimp only [Cond.holds]
      rw [RegFile.get_x0]
      obtain ⟨-, -, -, hx30, -⟩ := hinv
      rw [hh] at hx30
      exact hx30
    show encodes (toyRun prog (ToyState.init gas₀) cap) rf ws
    rw [toyRun_halted_of_le hile hhalt]
    exact hinv

end InterpLoopDemo
end SAsm
end EvmAsm.Rv64
