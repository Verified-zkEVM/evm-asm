# evm-asm Separation Logic Tactics

User guide for the frame automation tactics in `EvmAsm/Tactics/`.

## Overview

| Tactic | File | Purpose |
|--------|------|---------|
| `runBlock` | `RunBlock.lean` | Verify a multi-instruction block (main workhorse) |
| `seqFrame` | `SeqFrame.lean` | Compose two `cpsTriple` specs with automatic framing |
| `xcancel` | `XCancel.lean` | Match/cancel separation logic atoms, compute frame |
| `xperm` | `XPerm.lean` | Prove `P = Q` for AC-permutations of `sepConj` chains |
| `@[spec_gen]` | `SpecDb.lean` | Register instruction specs for auto-resolution |
| `#spec_db` | `SpecDb.lean` | Print all registered instruction specs |

## runBlock

The primary tactic for verifying basic blocks. Composes instruction specs
with automatic framing, address normalization, and postcondition permutation.

### Auto mode (preferred)

When called with no arguments, `runBlock` resolves specs from the `@[spec_gen]`
database by inspecting the goal's precondition:

```lean
theorem add_limb0_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 sum carry : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 20)
      ((base ↦ᵢ .LW .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LW .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .ADD .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SLTU .x5 .x7 .x6) **
       ((base + 16) ↦ᵢ .SW .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      (...) := by
  runBlock  -- verifies all 5 instructions automatically
```

### Manual mode

Pass spec hypotheses when auto-resolution can't handle composite specs:

```lean
theorem add_limb_carry_spec ... := by
  have s1 := add_limb_carry_spec_phase1 ...
  have s2 := add_limb_carry_spec_phase2 ...
  runBlock s1 s2
```

### Requirements

- Goal must be a `cpsTriple entry exit pre post`
- **Auto mode**: precondition must contain `instrAt` (`↦ᵢ`) atoms with concrete
  instruction constructors (e.g., `.ADD .x7 .x7 .x6`)
- **Manual mode**: each argument must be a `cpsTriple` proof

### Debugging

Enable trace output to see what `runBlock` is doing:

```lean
set_option trace.runBlock true in
theorem my_spec ... := by runBlock
```

This shows:
- Number of instructions and state atoms detected
- Which specs are being tried for each instruction
- Which spec was selected
- Composition progress

### Common failure modes

| Symptom | Cause | Fix |
|---------|-------|-----|
| "no @[spec_gen] specs registered for ..." | Instruction not in database | Add `@[spec_gen]` to a spec, or use manual mode |
| "cannot solve proof obligation: ..." | Missing hypothesis (e.g., `isValidMemAccess`) | Add hypothesis to theorem statement |
| "no spec could be instantiated" | Register/memory state doesn't match any spec variant | Check spec variants with `#spec_db`; may need a new spec |
| "h2's precondition atom not found..." | Specs don't chain (postcondition mismatch) | Check spec ordering and intermediate state |

## seqFrame

Composes two `cpsTriple` specs with automatic frame computation:

```lean
have s1 : cpsTriple base mid P Q1 := ...
have s2 : cpsTriple mid exit_ P2 Q2 := ...
seqFrame s1 s2
-- Produces: cpsTriple base exit_ P (Q2 ** Frame)
-- where Frame = Q1 atoms not consumed by P2
```

If the goal is a `cpsTriple`, `seqFrame` tries to close it (with postcondition
permutation). Otherwise, the result is introduced as a hypothesis named `s1s2`.

## xcancel

Cancellation tactic for separation logic assertions:

```lean
-- h : (A ** B ** C ** D) s
-- Goal: (A ** C ** ?Frame) s
xcancel h
-- Closes goal, unifying ?Frame with (B ** D)
```

## xperm

Proves equality between AC-permutations of `sepConj` chains:

```lean
example : (A ** B ** C) = (C ** A ** B) := by xperm
```

Used internally by all other tactics. Also available as `xperm_hyp` (in
`XSimp.lean`) for rewriting hypotheses.

## @[spec_gen] and #spec_db

### Registering specs

Tag single-instruction specs with `@[spec_gen]`:

```lean
@[spec_gen]
theorem lw_spec_gen (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) **
       ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((addr ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) **
       ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := ...
```

Requirements:
- Must be `cpsTriple`, `cpsBranch`, or `cpsHaltTriple`
- Precondition must contain an `instrAt` (`↦ᵢ`) atom
- The instruction must be a concrete constructor application
- Multiple specs per instruction are allowed (tried in registration order)

### Inspecting the database

```lean
#spec_db  -- prints all registered specs grouped by instruction constructor
```

### Auto-resolution algorithm

For each instruction in the precondition, `runBlock` (auto mode):
1. Extracts the instruction constructor name (e.g., `EvmAsm.Instr.LW`)
2. Looks up all `@[spec_gen]` entries for that constructor
3. For each candidate spec:
   a. Creates metavariables for all universally quantified parameters
   b. Unifies the spec's `instrAt`, `regIs`, and `memIs` atoms against the state
   c. Solves proof obligations: `mkDecideProof` for `rd ≠ .x0`/`rd ≠ rs`,
      local context search for other hypotheses, `bv_omega` as fallback
4. Returns the first successfully instantiated spec

## Architecture

```
xperm (AC permutation proofs)
  └── xcancel (cancellation with frame computation)
        └── seqFrame (two-spec composition with framing)
              └── runBlock (multi-spec composition)
                    └── SpecDb (@[spec_gen] registry for auto-resolution)
```

Each layer builds on the one below. All tactics work at the `MetaM` level,
constructing proof terms directly rather than using tactic combinators.
