# Port playbook — verify one guest routine, end to end

The single entry point for turning one unverified guest routine into a
verified, deployed one. Follow it top to bottom; every step points at ONE
exemplar to copy and ONE reference section for trouble. Do not read the long
docs end-to-end — this page routes you to the paragraph you need.

**Your target**: a bead like "verify `<routine>`" whose acceptance is
`scripts/port-check.sh <file>` green + (if emitted code changed) an EEST A/B.
Where your routine fits in the big picture: `docs/agents/top-theorem-ledger.md`.

## Step 0 — scope the routine (5 min)

```bash
grep -rn "<routine>" EvmAsm/Codegen/Programs/ | head        # find the asm def
python3 scripts/asm_to_program.py coverage | grep <routine>   # conversion class, if covered
```

Read the asm body once and classify:

| Class | Signs | Exemplar to copy | Recipe |
|---|---|---|---|
| **A. Byte-wise reader** (SSZ/RLP offset chase, no stores) | only `lbu`/`slli`/`or`, input-relative | `EvmAsm/Stateless/SSZ/Decode/ChainIdSAsm.lean` | sasm-howto §7 |
| **B. Branchy pure leaf** (computes a value in regs) | `beq/blt` tree or branchless `sltiu/sll`, no memory | `EvmAsm/Codegen/Programs/ClzSAsm.lean` (`clzFn_spec`) + `EvmAsm/Stateless/SSZ/Decode/ActiveForkSAsm.lean` | sasm-howto §6 "Branchy straight-line code" |
| **C. Store/copy leaf** (writes a window: memcpy, byte-reverse, encode) | `sb/sd` into an output window | `rev4Fn`/`revCellFn` in `EvmAsm/Rv64/SAsm/ExamplesVc.lean` | sasm-howto §6 "Multi-dword / Byte-granularity focus blocks" |
| **D. Loop over data** (RLP walk, list scan, table search) | bounded `while`, cursor regs | `treeMinFn` in `EvmAsm/Rv64/SAsm/TreeDemo.lean`; RLP: `EvmAsm/Codegen/Programs/RlpWalk.lean` | sasm-howto §4 (loops) + §6 (tree-walk template) |
| **E. Arena mutator** (node DB append, MPT insert, exec-log) | stores through computed pointers into a `.data` arena | `treeInsertFn` in `EvmAsm/Rv64/SAsm/TreeInsert.lean` | sasm-howto §6 (ghost/focus/harvest) |
| **F. Caller / composite** (calls other routines) | `jal`/`jalr` to named fns | `RaSpill.lean` two-level demo; indirect: `CallRegDemo` | sasm-howto §5 (calls) |
| **G. Accelerator bridge** (keccak/sha256/arith256 CSR) | `.4byte 0x800…073` words | `EvmAsm/Rv64/ZiskAccel.lean` KATs | design §3.3.1; beads 4ch8f.17/.18 |
| **H. Monolithic orchestration** | hundreds of lines, many calls | **do not port whole** — file child beads per callee (callee-first), then port as class F | ledger rows 8–9 |

If the routine's callees are unverified, STOP and do the callees first (or file
beads for them). Callee-first is the epic's dependency rule.

## Step 1 — scaffold (10 min)

```bash
python3 scripts/gen-port-kit.py <routine> \
  --class A --out EvmAsm/Stateless/<Area>/<Routine>SAsm.lean
```

This emits: the `Program`/SAsm skeleton converted from the asm string, an
`Fn.Spec` stub with named pre/post holes, `#guard` pins (length +
position-independence), the correspondence-theorem stub, and the EEST A/B
command block. If the generator does not support the routine (composite,
la-heavy), copy the exemplar file for your class and rename.

## Step 2 — state the contract (the thinking step)

- **Pre**: exactly the implicit assumptions of the asm (offsets in range,
  alignment, pointer non-null). Pull ghost values from the input buffer with
  `leByte`/`leU32`/`leU64` (ChainIdSAsm pattern).
- **Post**: pin the ABI registers downstream code documents, plus the memory
  window written. Use the same index spellings in pre and post (they must match
  syntactically — sasm-howto §7.4).
- Postcondition with ≥3 `let`s → wrap in `@[irreducible] def …Post` + `_unfold`
  + `_weaken` (docs/agents/proof-patterns.md §Bundling).
- **Vacuity check**: your pre must be satisfiable — reuse `inputRegion_wf`
  or state a small witness lemma. A triple with an unsatisfiable pre will be
  rejected in review.

## Step 3 — prove

Run `vcgen`, then close VCs in order. Standard closers, try in this order:

```
and_intros <;> first | trivial | omega | bv_omega
by rv64_addr            -- address-arithmetic goals
decide                  -- concrete, closed goals only (coerce fvars first)
simp only [...]         -- keep BitVec form; NO bare simp on sepConj chains
```

Known trap (found by the acceptance-test port, `Codegen/Proofs/U256IsZeroSpec.lean`):
`runBlock` cannot extend singleton specs to a goal whose CodeReq is
`CodeReq.ofProg <list-literal Program def>` — it reports
"don't know how to synthesize placeholder" at every `have` line while its own
trace shows all steps green. Fix: unfold to the union chain first:
`simp only [<prog def>, CodeReq.ofProg_cons, CodeReq.ofProg_nil]` before `runBlock`.
Also: rewrite `signExtend12`-literal mismatches in spec hypotheses
(`rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide] at SL`).

When a VC will not close, look up the SYMPTOM in this order:
1. sasm-howto §8 (pitfalls — check here first, most failures are listed);
2. docs/agents/proof-patterns.md (xperm cliffs, defeq traps, omega blowups);
3. GRIND.md rules of thumb (what NOT to simp/grind).

Hard rules: no `native_decide`, no `bv_decide`, no `maxHeartbeats`/`maxRecDepth`
bumps, zero warnings. If you are stuck after ~3 distinct attempts on the same
VC, STOP: write what you tried and the exact goal state into the bead
(`bd update <id> --notes="..."`), leave the port unlanded, and move on. A
documented blocker is a good outcome; a `sorry` or a weakened spec is not.

## Step 4 — deploy + check

```bash
scripts/port-check.sh EvmAsm/Stateless/<Area>/<Routine>SAsm.lean
```

(green = builds warning-free, no forbidden tactics, new theorems are
3-classical-axioms clean, `#guard` pins present).

If you swapped the routine into emitted code (`Entry.lean` or a Codegen
program): run the EEST A/B from the generated comment block (sasm-howto §7.6).
Failures acceptable only if identical on both legs.

## Step 5 — close out

1. Update `docs/agents/top-theorem-ledger.md` if your routine completes a row.
2. Update PLAN.md (one line in the SAsm/Stateless section).
3. `bd close <bead>` only after the PR lands on main (AGENTS.md closure rules).
4. PR: small (one routine or two), body ends with the standard footer.
