/-
  EvmAsm.Evm64.JumpTable

  Slice 1 of GH #106 (opcode dispatch via jump table).

  Defines the `dispatchTableIs` separation-logic assertion describing a
  256-entry handler-address table laid out at consecutive doubleword
  cells in RV64 memory:

      base + 0   ↦ₘ handlers[0]
      base + 8   ↦ₘ handlers[1]
      ...
      base + 8·k ↦ₘ handlers[k]
      ...
      base + 8·255 ↦ₘ handlers[255]

  This module only fixes the layout and proves the basic projection
  (`getMem (base + 8·opcode) = handlers[opcode]` from
  `dispatchTableIs.holdsFor`). The dispatch RV64 program (LBU/SLLI/ADD/
  LD/JALR sequence) and its Hoare triple land in subsequent slices
  (`evm-asm-kvygx`, `evm-asm-afkny`, `evm-asm-3ho93`).

  No new tactics, no existing files modified — strictly additive.
-/

module

public import EvmAsm.Rv64.Basic
public import EvmAsm.Rv64.SepLogic
public import EvmAsm.Evm64.Dispatch

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Auxiliary builder: assertion describing handler-address dwords for
    the `count` entries with indices `[start, start + count)`, where
    `start + count ≤ 256`.

    Entries are chained by `**` from index `start` upward; the recursion
    is on the residual `count`. The companion `dispatchTableIs` below
    fixes `start = 0` and `count = 256`. -/
def dispatchTableIs.aux (base : Word) (handlers : Fin 256 → Word) :
    (start : Nat) → (count : Nat) → Assertion
  | _,     0     => empAssertion
  | start, n + 1 =>
    if h : start < 256 then
      ((base + BitVec.ofNat 64 (8 * start)) ↦ₘ handlers ⟨start, h⟩)
        ** dispatchTableIs.aux base handlers (start + 1) n
    else
      empAssertion

/-- Layout assertion for a 256-entry RV64 jump table at base address
    `base`. Entry `i` holds the handler address `handlers i` in the
    doubleword cell at `base + 8·i`. -/
def dispatchTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableIs.aux base handlers 0 256

/-- Convenience alias: `evmJumpTableIs` is identical to
    `dispatchTableIs` but reads more naturally inside EVM-level specs. -/
def evmJumpTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableIs base handlers

@[simp] theorem evmJumpTableIs_eq (base : Word) (handlers : Fin 256 → Word) :
    evmJumpTableIs base handlers = dispatchTableIs base handlers := rfl

/-! ### Projection: read one handler-address entry from the layout. -/

/-- Helper: `dispatchTableIs.aux` with `count = 0` is `empAssertion`. -/
@[simp] theorem dispatchTableIs.aux_zero (base : Word)
    (handlers : Fin 256 → Word) (start : Nat) :
    dispatchTableIs.aux base handlers start 0 = empAssertion := rfl

/-- Helper: unfold one step of the auxiliary builder when `start < 256`. -/
theorem dispatchTableIs.aux_succ (base : Word)
    (handlers : Fin 256 → Word) {start : Nat} (h : start < 256) (n : Nat) :
    dispatchTableIs.aux base handlers start (n + 1)
      = (((base + BitVec.ofNat 64 (8 * start)) ↦ₘ handlers ⟨start, h⟩)
        ** dispatchTableIs.aux base handlers (start + 1) n) := by
  simp only [dispatchTableIs.aux, dif_pos h]

/-- The auxiliary layout assertion forces the dword at
    `base + 8·(start + k)` to read back the corresponding handler entry,
    for any `k < count` with `start + count ≤ 256`. -/
theorem dispatchTableIs.aux_getMem
    {base : Word} {handlers : Fin 256 → Word}
    {start count : Nat} (hsum : start + count ≤ 256)
    {s : MachineState}
    (hP : (dispatchTableIs.aux base handlers start count).holdsFor s)
    (k : Nat) (hk : k < count) :
    s.getMem (base + BitVec.ofNat 64 (8 * (start + k)))
      = handlers ⟨start + k, by omega⟩ := by
  induction count generalizing start k with
  | zero => omega
  | succ n ih =>
    have hstart : start < 256 := by omega
    rw [dispatchTableIs.aux_succ base handlers hstart n] at hP
    have hP_left  := holdsFor_sepConj_elim_left  hP
    have hP_right := holdsFor_sepConj_elim_right hP
    match k with
    | 0 =>
      -- The leading cell directly matches the head sepConj entry.
      have hmem := (holdsFor_memIs.mp hP_left).1
      simpa [Nat.add_zero] using hmem
    | k' + 1 =>
      -- Step into the tail: shift `start ↦ start+1`, `k' < n`.
      have hk' : k' < n := Nat.lt_of_succ_lt_succ hk
      have hsum' : (start + 1) + n ≤ 256 := by omega
      have hrec := ih (start := start + 1) hsum' hP_right k' hk'
      have hidx : start + (k' + 1) = (start + 1) + k' := by omega
      have hfin :
          (⟨start + (k' + 1), by omega⟩ : Fin 256)
            = ⟨(start + 1) + k', by omega⟩ := by
        apply Fin.ext; exact hidx
      rw [hfin, show (8 * (start + (k' + 1))) = (8 * ((start + 1) + k')) by omega]
      exact hrec

/-- **Projection lemma.** If the 256-entry jump-table layout holds at
    `base`, then for every opcode byte `opcode : Fin 256` the dword cell
    at `base + 8·opcode` reads back the corresponding handler address
    `handlers opcode`. -/
theorem dispatchTableIs_getMem
    {base : Word} {handlers : Fin 256 → Word}
    {s : MachineState}
    (hP : (dispatchTableIs base handlers).holdsFor s)
    (opcode : Fin 256) :
    s.getMem (base + BitVec.ofNat 64 (8 * opcode.val))
      = handlers opcode := by
  have hk : opcode.val < 256 := opcode.isLt
  have h := dispatchTableIs.aux_getMem
    (base := base) (handlers := handlers)
    (start := 0) (count := 256) (by omega) hP opcode.val hk
  -- `start = 0` collapses `start + k = k` and `⟨k, _⟩ = opcode`.
  have hfin : (⟨0 + opcode.val, by omega⟩ : Fin 256) = opcode := by
    apply Fin.ext; simp
  simpa [Nat.zero_add, hfin] using h


/-! ### Constructing a `Fin 256 → Word` table with an INVALID default

This block lifts a *partial* opcode → handler-address map (`Fin 256 → Option
Word`, only set for implemented opcodes) into the *total* `Fin 256 → Word`
shape that the `dispatchTableIs` layout takes, by routing every unset opcode
to a single `invalidHandler` address. This is layer (a) of GH #106 slice 4
(beads `evm-asm-3ho93` / `evm-asm-hbdu9`); the matching semantic step —
proving that JALR-ing to `invalidHandler` drives `EvmState` into its invalid
status — is layer (b) and lands once `dispatch_spec` (slice 3) is in.
-/

/-- Total handler-address table built from a partial opcode → handler map
    and a fall-back `invalidHandler` address. Opcodes for which `lookup`
    returns `none` are routed to `invalidHandler`. -/
def jumpTableOfHandlers
    (invalidHandler : Word) (lookup : Fin 256 → Option Word) : Fin 256 → Word :=
  fun opcode => (lookup opcode).getD invalidHandler

/-- Lookup is the implemented handler when the partial map covers the
    opcode. -/
@[simp] theorem jumpTableOfHandlers_some
    (invalidHandler : Word) (lookup : Fin 256 → Option Word)
    (opcode : Fin 256) (h : Word) (hp : lookup opcode = some h) :
    jumpTableOfHandlers invalidHandler lookup opcode = h := by
  simp [jumpTableOfHandlers, hp]

/-- Lookup falls back to `invalidHandler` when the partial map does not
    cover the opcode — this is what makes a transition to INVALID the
    default for unimplemented opcodes once `dispatch_spec` is wired in. -/
@[simp] theorem jumpTableOfHandlers_none
    (invalidHandler : Word) (lookup : Fin 256 → Option Word)
    (opcode : Fin 256) (hp : lookup opcode = none) :
    jumpTableOfHandlers invalidHandler lookup opcode = invalidHandler := by
  simp [jumpTableOfHandlers, hp]

/-- The all-`none` partial map produces the constant `invalidHandler` table
    — useful as a base case for incrementally extending coverage. -/
@[simp] theorem jumpTableOfHandlers_const_none
    (invalidHandler : Word) (opcode : Fin 256) :
    jumpTableOfHandlers invalidHandler (fun _ => none) opcode
      = invalidHandler := by
  simp [jumpTableOfHandlers]

/-! ### Decoder-backed handler address tables

The pure decoder (`EvmOpcode.decodeByte?`) tells us whether an opcode byte is
currently modeled. The jump table, however, is indexed by raw bytes and stores
RV64 handler addresses. These helpers bridge the two surfaces: decoded opcodes
use their opcode-address map, while undecoded bytes fall through to the
INVALID handler address.
-/

/-- Partial raw-byte lookup obtained by decoding each byte to an `EvmOpcode`
    and then mapping decoded opcodes to handler addresses. -/
def opcodeHandlerAddressLookup
    (handlers : EvmOpcode → Word) : Fin 256 → Option Word :=
  fun opcodeByte => (EvmOpcode.decodeByte? opcodeByte.val).map handlers

/-- Total raw-byte jump table for opcode handlers, with undecoded bytes routed
    to the INVALID handler address. -/
def jumpTableOfOpcodes
    (invalidHandler : Word) (handlers : EvmOpcode → Word) : Fin 256 → Word :=
  jumpTableOfHandlers invalidHandler (opcodeHandlerAddressLookup handlers)

@[simp] theorem opcodeHandlerAddressLookup_some
    (handlers : EvmOpcode → Word) (opcodeByte : Fin 256) (opcode : EvmOpcode)
    (h_decode : EvmOpcode.decodeByte? opcodeByte.val = some opcode) :
    opcodeHandlerAddressLookup handlers opcodeByte = some (handlers opcode) := by
  simp [opcodeHandlerAddressLookup, h_decode]

@[simp] theorem opcodeHandlerAddressLookup_none
    (handlers : EvmOpcode → Word) (opcodeByte : Fin 256)
    (h_decode : EvmOpcode.decodeByte? opcodeByte.val = none) :
    opcodeHandlerAddressLookup handlers opcodeByte = none := by
  simp [opcodeHandlerAddressLookup, h_decode]

@[simp] theorem jumpTableOfOpcodes_decode_some
    (invalidHandler : Word) (handlers : EvmOpcode → Word)
    (opcodeByte : Fin 256) (opcode : EvmOpcode)
    (h_decode : EvmOpcode.decodeByte? opcodeByte.val = some opcode) :
    jumpTableOfOpcodes invalidHandler handlers opcodeByte = handlers opcode := by
  simp [jumpTableOfOpcodes, h_decode]

@[simp] theorem jumpTableOfOpcodes_decode_none
    (invalidHandler : Word) (handlers : EvmOpcode → Word)
    (opcodeByte : Fin 256)
    (h_decode : EvmOpcode.decodeByte? opcodeByte.val = none) :
    jumpTableOfOpcodes invalidHandler handlers opcodeByte = invalidHandler := by
  simp [jumpTableOfOpcodes, h_decode]

/-- If a decoder-backed jump table is present in RV64 memory, an unsupported
    opcode byte reads back the INVALID handler address. This is the byte-level
    layout bridge needed before the dispatch proof wires the loaded address to
    the INVALID handler path. -/
theorem jumpTableOfOpcodes_decode_none_getMem
    {base invalidHandler : Word} {handlers : EvmOpcode → Word}
    {s : MachineState}
    (hP : (dispatchTableIs base (jumpTableOfOpcodes invalidHandler handlers)).holdsFor s)
    (opcodeByte : Fin 256)
    (h_decode : EvmOpcode.decodeByte? opcodeByte.val = none) :
    s.getMem (base + BitVec.ofNat 64 (8 * opcodeByte.val))
      = invalidHandler := by
  rw [dispatchTableIs_getMem hP opcodeByte]
  exact jumpTableOfOpcodes_decode_none invalidHandler handlers opcodeByte h_decode

/-- Decoder-backed memory reads return the handler address assigned to the
    decoded opcode when the byte is supported. -/
theorem jumpTableOfOpcodes_decode_some_getMem
    {base invalidHandler : Word} {handlers : EvmOpcode → Word}
    {s : MachineState}
    (hP : (dispatchTableIs base (jumpTableOfOpcodes invalidHandler handlers)).holdsFor s)
    (opcodeByte : Fin 256) (opcode : EvmOpcode)
    (h_decode : EvmOpcode.decodeByte? opcodeByte.val = some opcode) :
    s.getMem (base + BitVec.ofNat 64 (8 * opcodeByte.val))
      = handlers opcode := by
  rw [dispatchTableIs_getMem hP opcodeByte]
  exact jumpTableOfOpcodes_decode_some invalidHandler handlers opcodeByte opcode h_decode

/-! ### Entry / rest split.

The dispatch RV64 program needs to LD one specific table entry; the LD
spec consumes a single `↦ₘ` cell. To frame it against the 256-entry
chain we expose the entry as a head and bundle the surrounding entries
into a residual `Assertion`. The split lives at the layout level
(equality of `Assertion`s), so callers can directly rewrite both the
hypothesis and the goal during the dispatch_spec proof (slice 3,
`evm-asm-afkny`).

The construction uses two `aux` chains glued either side of the chosen
entry; this is symmetric in both directions, unlike the existing
`aux_getMem` projection which only goes layout → memory.
-/

namespace dispatchTableIs

/-- Split a generic `aux` chain at one interior position.

If `start + a + 1 + b ≤ 256`, then the `(a + 1 + b)`-cell auxiliary
chain decomposes into:

* the prefix of the first `a` cells (`aux base handlers start a`),
* the singled-out entry at index `start + a`,
* the suffix of the next `b` cells (`aux base handlers (start+a+1) b`).
-/
theorem aux_split (base : Word) (handlers : Fin 256 → Word)
    (start a b : Nat) (h : start + a + 1 + b ≤ 256) :
    aux base handlers start (a + 1 + b)
      = (aux base handlers start a
        ** ((base + BitVec.ofNat 64 (8 * (start + a))) ↦ₘ handlers ⟨start + a, by omega⟩)
        ** aux base handlers (start + a + 1) b) := by
  induction a generalizing start with
  | zero =>
    -- prefix is empty, suffix carries the rest.
    have hstart : start < 256 := by omega
    have hsum' : start + 1 + b ≤ 256 := by omega
    have h1 : (0 + 1 + b : Nat) = b + 1 := by omega
    rw [h1, aux_succ base handlers hstart b]
    simp only [aux, sepConj_emp_left', Nat.add_zero]
  | succ a ih =>
    -- Peel one entry off the front, recurse on the tail with start+1.
    have hstart : start < 256 := by omega
    have hrec : (start + 1) + a + 1 + b ≤ 256 := by omega
    have h1 : ((a + 1) + 1 + b : Nat) = (a + 1 + b) + 1 := by omega
    rw [h1, aux_succ base handlers hstart (a + 1 + b),
        ih (start + 1) hrec, aux_succ base handlers hstart a]
    -- Massage the `start + (a + 1)` indices to match `(start + 1) + a`.
    have hidx : start + (a + 1) = (start + 1) + a := by omega
    have hfin :
        (⟨start + (a + 1), by omega⟩ : Fin 256)
          = ⟨(start + 1) + a, by omega⟩ := by
      apply Fin.ext; exact hidx
    rw [hfin, show start + (a + 1) + 1 = (start + 1) + a + 1 from by omega,
        show 8 * (start + (a + 1)) = 8 * ((start + 1) + a) from by omega,
        ← sepConj_assoc']

end dispatchTableIs

/-- **Entry/rest split.** The 256-entry jump-table layout decomposes
    into the singled-out entry at `opcode` and a residual chain
    `dispatchTableIs.rest` covering all other indices. This is the form
    the dispatch RV64 program's LD step consumes during the slice-3
    Hoare-triple proof. -/
def dispatchTableIs.rest (base : Word) (handlers : Fin 256 → Word)
    (opcode : Fin 256) : Assertion :=
  dispatchTableIs.aux base handlers 0 opcode.val
    ** dispatchTableIs.aux base handlers (opcode.val + 1) (255 - opcode.val)

theorem dispatchTableIs_split (base : Word) (handlers : Fin 256 → Word)
    (opcode : Fin 256) :
    dispatchTableIs base handlers
      = (((base + BitVec.ofNat 64 (8 * opcode.val)) ↦ₘ handlers opcode)
        ** dispatchTableIs.rest base handlers opcode) := by
  have hk : opcode.val < 256 := opcode.isLt
  have h : (0 : Nat) + opcode.val + 1 + (255 - opcode.val) ≤ 256 := by omega
  have heq : opcode.val + 1 + (255 - opcode.val) = 256 := by omega
  have hsplit := dispatchTableIs.aux_split base handlers 0 opcode.val (255 - opcode.val) h
  -- Rewrite count `0 + opcode.val + 1 + (255 - opcode.val) = 256`.
  rw [show (opcode.val + 1 + (255 - opcode.val) : Nat) = 256 from heq] at hsplit
  -- Realign Fin indexing: `⟨0 + opcode.val, _⟩ = opcode`.
  have hfin :
      (⟨0 + opcode.val, by omega⟩ : Fin 256) = opcode := by
    apply Fin.ext; simp
  rw [hfin] at hsplit
  -- `dispatchTableIs` and `rest` are direct unfoldings.
  show dispatchTableIs.aux base handlers 0 256 = _
  rw [hsplit]
  unfold dispatchTableIs.rest
  -- Goal: `prefix ** entry ** suffix = entry ** prefix ** suffix`.
  ac_rfl


end EvmAsm.Evm64
