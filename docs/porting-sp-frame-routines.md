# Porting sp-frame guest routines (FramePort tactics)

**Audience:** any agent that can write Lean by pattern-matching against
templates. You do NOT need to understand the separation logic to port a
routine in the first two tiers below — you need to classify your routine,
copy the right skeleton, fill in the routine-specific values, and run the
definition-of-done checklist. Anything the templates don't cover is an
**escalation**, not something to improvise.

Landed by PR #9982 (bead `evm-asm-4ch8f.76`-tree). The tactics live in
`EvmAsm/Rv64/SAsm/FramePort.lean`; the underlying composition lemmas in
`EvmAsm/Rv64/SAsm/AbiFrame.lean` (`abiFrame_spec`),
`AbiFrameLoop.lean` (`countdownLoop_spec`),
`AbiFrameLoopBottom.lean` (`countdownLoopBottom_spec`, `dwordsIs`),
`AbiFrameCall.lean` (`callWithin_spec`, `abiFrameCall_spec`, `stackFree`).

## 1. What this is / when to use it

Many emitted guest routines use a C-ABI **stack frame**: an
`addi sp, sp, -N` prologue that saves `ra` and callee-saved `s`-registers,
a body that may loop and/or `jal ra, callee`, and an epilogue that restores
everything and `ret`s. The structured SAsm layer (`Fn`/`vcgen`) cannot
express these (it exposes only caller registers). The **ABI-frame
construct** verifies them at the `cpsTripleWithin` machine level:
`abiFrame_spec` lifts a single-exit body triple into the whole
prologue·body·epilogue·ret routine, *proving* that `sp`, `ra`, and every
saved `s`-register are restored to their entry values. The **FramePort
tactics** discharge all the boilerplate side-conditions, so your port is
only: the body's instruction list, the genuine postcondition, and (if there
is a loop) its invariant.

## 2. Triage: classify your routine before you start

Find the routine's `_prog : Program` def under `EvmAsm/Codegen/Programs/`.
It is an sp-frame routine iff it starts with `.ADDI .x2 .x2 (-N)` followed
by `.SD .x2 …` saves and ends with matching `.LD`s, `.ADDI .x2 .x2 (N)`,
`.JALR .x0 .x1 0`.

| tier | how to recognize | tools | who |
|---|---|---|---|
| **A. straight-line body** | body has no `JAL`/`JALR` and no backward branch | `abi_frame` + `runBlock`/manual per-instruction specs | any agent (this doc suffices) |
| **B. body with one countdown loop** | a backward `JAL .x0 (-…)` with a `BEQ ctr, x0, exit` header (**top-guard**), or a backward `BNE ctr, x0, (-…)` at the loop end (**do-while**) | tier A + `countdown_loop` (top-guard) / `countdown_loop_bottom` (do-while) | any agent, if the invariant is a simple accumulator/cursor |
| **C. cross-call** | body contains `.JAL .x1 …` (links `ra`) | tier A/B + `callWithin_spec` / `frame_call` — but **every callee needs a whole-routine contract first**; if the callee has an `Fn.Spec`, DERIVE it with the adapter (§5a) instead of hand-writing | agent may proceed ONLY if all callees have flat contracts or `Fn.Spec`s to adapt; else port the callees first (bottom-up) or escalate |
| **D. escalate** | see below | — | Opus/Fable |

**Escalate (do not attempt) when:**

- the routine is **large** (≳ 40–50 instructions): the `abi_frame` wrapper
  hits elaboration limits around the 84-instruction scale
  (`ParentHeaderFrame.lean` keeps an explicit `abiFrame_spec` application
  for this reason — that form needs fluency);
- the body has **multiple exits / branch reconvergence** (status codes,
  early-outs) — the unified-disjunctive-post technique
  (`ParentHeaderFrame.phmwCore_spec`) is not mechanical;
- the loop is **not** a plain countdown over one register decremented by 1
  per iteration (novel shapes need a new loop lemma);
- any load/store in the body is **misaligned** in the verified model
  (e.g. `lwu` from a pointer that is not provably 4-aligned): the model
  rejects it even though ziskemu tolerates it. Such routines need a
  **re-emit** drop-in (byte change + A/B parity — see §7), which needs
  maintainer coordination;
- a callee has no contract and is itself out of your tier.

**Byte-transparent vs re-emit** (check this FIRST — it decides your whole
workflow):

```lean
-- Put this next to the existing <name>_prog and try to make it pass:
#guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) myFrame myBody = <name>_prog
```

If you can choose `myFrame`/`myBody` (just split the existing instruction
list: prologue = first `1 + |frame|` instrs, epilogue = last `|frame| + 2`)
so the `#guard` passes, the routine is **byte-transparent**: you verify the
EXISTING bytes, no guest-image change, **no ziskemu/EEST A/B needed**.
If the emitted code doesn't fit the shape (misaligned access, early-exit
loop, …), a **re-emit** is required — that is a guest-byte change with the
full drop-in discipline (§7) and is tier D unless you've done one before.

## 3. The 4-step recipe

1. **Define the routine pieces + byte-tie** (in a new
   `EvmAsm/Codegen/Programs/<Name>SAsm.lean` if the routine references
   `GuestAddrs`, else a new `EvmAsm/Rv64/SAsm/…` file):

   ```lean
   def myFrame : FrameDesc := [(.x1, 0), (.x8, 8)]      -- (reg, slot offset): ra FIRST at 0
   def myBody : List Instr := [ … ]                     -- the body slice of the emitted prog
   #guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) myFrame myBody = <name>_prog
   theorem myProg_eq :
       abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) myFrame myBody = <name>_prog := rfl
   def myCr : CodeReq := CodeReq.ofProg (BASE : Word) <name>_prog
   ```

   `BASE` is the routine's guest address; tie it:
   `#guard GuestAddrs.<name> = 0x8003ABCD`. If the routine cross-calls an
   adjacent routine, make ONE `CodeReq` covering both
   (`CodeReq.ofProg loAddr (callee_prog ++ caller_prog)` when contiguous —
   see `Bn254Fq12SetOneSAsm.bnqCr`).

2. **State the genuine post and prove the body triple.** The body triple's
   statement shape is FIXED by `abiFrame_spec` (copy it from a worked
   example, §6): entry `BASE + BitVec.ofNat 64 (4 * (1 + myFrame.length))`,
   exit `BASE + BitVec.ofNat 64 (4 * (1 + myFrame.length + myBody.length))`,
   pre/post `(.x2 ↦ᵣ newSp) ** regsAt myFrame vals ** frameSlotsSaved … **
   callerPre/Post`. The `callerPost` must be the routine's REAL semantics —
   never `True`, never a weakened claim.

3. **Discharge the body** — the only creative part:
   - straight-line: one `have h<instr> := <op>_spec_gen_within …` per
     instruction (they are in `EvmAsm/Rv64/SyscallSpecs.lean`; all
     `@[spec_gen_rv64]`), chain with `runBlock h1 h2 …` over the local
     slice and lift with `lift_code`, or frame + sequence manually
     (templates in §6);
   - loop: prove the per-iteration triple, then `countdown_loop` /
     `countdown_loop_bottom`;
   - call: instantiate the callee's contract at `ret := A + 4` and use
     `callWithin_spec` / `frame_call`.

4. **Wrap:** `abi_frame (16 : BitVec 12) halign hbody` closes the
   whole-routine goal. Add `#print axioms <yourSpec>` at the end of the
   file and run the checklist (§8).

### What the tactics close vs what you supply

| goal | tactic | you supply |
|---|---|---|
| `P.pcFree` (any mix of `↦ᵣ`/`↦ₘ`/`memOwn`/`regOwn`/`⌜⌝`/`bytesRegion`/`stackFree`/`dwordsIs`/`regsAt`/`frameSlots*`) | `pcf` | nothing |
| `∀ a i, CodeReq.singleton …/ofProg … a = some i → cr a = some i` (all concrete) | `code_mem` | nothing |
| lifting a triple from a sub-CodeReq into the routine CodeReq | `lift_code h` (goal-directed) or `liftCode (cr' := myCr) h (by code_mem)` (term form) | the sub-triple `h` |
| the whole-routine `abiFrame_spec` conclusion + its ~12 side-conditions | `abi_frame posImm halign hbody` | `posImm` (the `+N` dealloc immediate), `halign : (ret &&& ~~~(1 : Word)) = ret` (a hypothesis of your theorem), `hbody` |
| a top-guard countdown loop + its 5 side-conditions | `countdown_loop exitOff hbody` | `exitOff : BitVec 13` (the header `BEQ`'s exit offset), `hbody : ∀ n, n < N → cpsTripleWithin …` |
| a do-while countdown loop | `countdown_loop_bottom backOff hbody` | `backOff : BitVec 13` (the tail `BNE`'s negative offset), `hbody` |
| one `jal ra` call + its side-conditions (frame-aware form) | `frame_call offset hcallee` | `offset : BitVec 21` (the `JAL`'s immediate), `hcallee` (callee contract at `ret := A + 4`) |
| a flat callee contract from an existing `Fn.Spec` | `Fn.retSpecFlat` + `cpsTripleWithin_peel_regOwns` + `regFileIs_eq_regAtoms` (§5a) | the leaf's `Fn.Spec`, its pinned post, the flat `Q` |
| the body semantics, the loop invariant, the genuine post | — | **you** |

## 4. Tactic reference (exact call shapes)

All are in `EvmAsm/Rv64/SAsm/FramePort.lean`; open namespace
`EvmAsm.Rv64.SAsm` (Codegen files: `open EvmAsm.Rv64 EvmAsm.Rv64.SAsm`).

- **`pcf`** — closes `P.pcFree`. No arguments. If it leaves a goal, your
  assertion contains a def it can't see through a combinator for — unfold
  your local def first (`unfold myInv` / `simp only [myInv]`), then `pcf`.

- **`code_mem`** — closes code-membership goals by kernel evaluation.
  Works when the CodeReq, addresses, and instructions are all concrete
  (literals or `GuestAddrs` constants). No arguments.

- **`lift_code h`** — tactic form; the goal must be
  `cpsTripleWithin n A B myCr P Q` and `h` the same triple over a
  sub-CodeReq (a `CodeReq.singleton`, an `ofProg` slice, a loop core).
  **Term form** (needed inside `have hx := …` where there is no goal to
  read `myCr` from): `liftCode (cr' := myCr) h (by code_mem)`.
  Common pattern — single-instruction specs end at `addr + 4`; normalize
  the literal FIRST or the later gluing fails on `0x…C + 4` vs `0x…10`:

  ```lean
  have hmv := mv_spec_gen_within .x8 .x10 dst arb8 (0x8003060C : Word) (by decide)
  rw [show (0x8003060C : Word) + 4 = (0x80030610 : Word) from by decide] at hmv
  have hmvC := liftCode (cr' := bnqCr) hmv (by code_mem)
  ```

- **`abi_frame posImm halign hbody`** — closes the standard
  whole-routine goal. `posImm` is the epilogue's positive `BitVec 12`
  immediate (e.g. `(16 : BitVec 12)`); `halign` is your theorem's
  alignment hypothesis (or `(by decide)` when `ret` is a concrete
  address); `hbody` a `have` with the exact body-triple shape (§3 step 2).
  Everything else (`hframe`/`hne`/`hbound`/`hprogBound`/`hret`/
  `hframeRestore`/`hcpF`/`hcpF'`/`hsub`) is discharged automatically.

- **`countdown_loop exitOff hbody`** — for the top-guard shape
  `hdr: beq ctr, x0, exitOff ; <body> ; jal x0, hdr`. The goal is the
  `countdownLoop_spec` conclusion: from `(ctr ↦ᵣ BitVec.ofNat 64 N) **
  (Reg.x0 ↦ᵣ 0) ** inv N` at `hdr` to `… inv 0` at the exit, in
  `N * (bodyStep + 1) + 1` steps. `hbody : ∀ n, n < N →
  cpsTripleWithin bodyStep (hdr + 4) hdr cr ((ctr ↦ᵣ ofNat (n+1)) ** x0 **
  inv (n+1)) ((ctr ↦ᵣ ofNat n) ** x0 ** inv n)`.

- **`countdown_loop_bottom backOff hbody`** — for the do-while shape
  `hdr: <body> ; tst: bne ctr, x0, backOff`. Conclusion runs `hdr →
  tst + 4` in `N * (bodyStep + 1)` steps, `N ≥ 1`; `hbody` runs
  `hdr → tst` decrementing the counter.

- **`frame_call offset hcallee`** — closes an `abiFrameCall_spec`-shaped
  goal (callee carves `stackFree spVal m`; the caller's frame slots ride
  in the explicit frame `F`). When you are building the call as a `have`
  (no goal), apply the lemma directly with named args — copy from
  `AbiFrameCallDemo.twiceFrame_spec`:

  ```lean
  have hcall1 := abiFrameCall_spec (A := 0x1008) (vOld := ret)
    (offset := (0xFF8 : BitVec 21))
    (F := ((newSp + signExtend12 (0 : BitVec 12)) ↦ₘ ret))
    (htarget := by decide) (hmem := by code_mem) (hpre := by pcf) (hF := by pcf)
    (hcallee := hb1)
  ```

  For a **frameless callee** (it allocates no stack), use the simpler
  `callWithin_spec` — see `Bn254Fq12SetOneSAsm` (§6.3).

## 5. Callee contracts (what a cross-call consumes)

A callee contract is a `cpsTripleWithin` from the callee's entry back to a
FREE return address, with `ra` pinned on both sides:

```lean
cpsTripleWithin n calleeEntry ret cr
  (((.x1 : Reg) ↦ᵣ ret) ** calleePre)
  (((.x1 : Reg) ↦ᵣ ret) ** calleePost)
-- for any ret with (ret &&& ~~~(1 : Word)) = ret
```

Two ways a callee gets one:

- **frameless callee** (no `addi sp` prologue): prove the contract
  directly at this shape — `bnqZeroFlat_spec` is the template
  (init ; loop ; `Fn.jalr_ret_spec` for the final `ret`, sequenced);
- **framed callee**: derive it from the callee's own `abiFrame_spec`
  instance and reshape (`regsAt`/`frameSlots*` unfolded, the frame slots
  presented as the caller's `stackFree` cells) — `bumpCall_spec` in
  `AbiFrameCallDemo.lean` is the template.

(`Fn.retSpec`/`FnHandle.sound` give structured-layer callees the same
outer shape, but their `asrtM` pre/post do NOT mix with the flat atoms
this guide uses — do not try to consume them directly.) If the callee has
no contract yet, port it first (bottom-up) or escalate.

### 5a. Adapting an existing `Fn.Spec` leaf into a callee (the adapter)

If the callee already has a structured-layer `Fn.Spec` (a `<Name>SAsm.lean`
file with `vcgen`), do NOT hand-write its flat contract — derive it with
the adapter `Fn.retSpecFlat` (`EvmAsm/Rv64/SAsm/FnFlat.lean`). Worked
pattern: `Bn254Fq12SetOneSAsm.bnqZeroFlat_spec` (~60 lines, no loop proof).
Skeleton:

```lean
theorem myCalleeFlat_spec (ret dst : Word) … (halign : …) :
    cpsTripleWithin (STEPS) (ENTRY : Word) ret myCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** regOwns myScratch ** …memory…)
      (((.x1 : Reg) ↦ᵣ ret) ** …post atoms… ** regOwns myScratch ** …) := by
  rw [show (STEPS : Nat) = (myFn ARGS).body.steps + 1 from rfl]
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns myScratch (by decide) (P := …tracked atoms…)
      (fun vf => ?_))
  have had := Fn.retSpecFlat (myFn ARGS) ENTRY (myFn_spec …) (by show …; decide)
    ret halign (fun r => if r = .x10 then dst else vf r) WS hlen
    (by …f.pre…) (fun _ _ _ h => h.2.2.2)   -- post pins A = empAssertion
    (Q := …) (fun rf' ws' hlen' hpost' hp hh => by …)
  rw [show (myFn ARGS).programRet ENTRY = myCallee_prog from rfl] at had
  have hadC := liftCode (cr' := myCr) had (by code_mem)
  -- unpack `regFileIs` (`regFileIs_eq_regAtoms`, `regAtoms_eq_regAtomsOf`,
  -- a local `exposedRegs_split`), convert memory (`dwordsIs_eq_bytesRegion`),
  -- final `cpsTripleWithin_weaken` + `xperm_hyp`.
```

**Three inherent side-conditions** (named in `FnFlat.lean`'s module doc —
check them BEFORE starting; each failure has a fix):

1. **Footprint width**: an adapted contract owns the WHOLE exposed register
   file (15 registers — that is what `Fn.Spec` claims), so the CALLER must
   own all of them across the call: `regOwns` riders for the ones it does
   not track (see `bnqRiders` in the worked file). A hand-written flat
   theorem can have a smaller footprint; the adapter trades that for zero
   per-callee proof.
2. **Post completeness**: the adapter carries exactly `f.post`. If your
   caller needs a final register value (e.g. the advanced `a0`), the
   callee's `Fn` post must pin it — strengthen the `Fn` post (the
   strongest-post already tracks it; e.g. `Bn254Fq12ZeroSAsm` gained
   `rf.get .x10 = dst + 384 ∧ rf.get .x7 = 0` with a ~10-line VC patch).
3. **Ambient pinning**: the callee's `pre`/`post`/loop invariant must pin
   the ambient `A = empAssertion` (add the conjunct; it threads through
   the strongest-post trivially).

## 6. Worked examples (copy these skeletons)

### 6.1 Straight-line body inside a frame — `AbiFrameCallDemo.bump`

File: `EvmAsm/Rv64/SAsm/AbiFrameCallDemo.lean` (synthetic; the corpus has
no call-free sp-frame routines, so straight-line bodies appear in real
life as segments of tier-B/C routines — the skeleton is identical).

```lean
def bumpFrame : FrameDesc := [(.x1, 0), (.x8, 8)]
def bumpBody : List Instr :=
  [ .MV .x8 .x10, .LD .x11 .x8 0, .ADDI .x11 .x11 1, .SD .x8 .x11 0 ]
#guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) bumpFrame bumpBody = bumpProgList
```

Body proof shape (per-instruction specs + `runBlock` over the local slice,
lifted, then framed with the untouched frame atoms), then the wrap:

```lean
have hbody : cpsTripleWithin 4
    ((0x2000 : Word) + BitVec.ofNat 64 (4 * (1 + bumpFrame.length))) … := by …
abi_frame (16 : BitVec 12) halign hbody
```

The theorem statement to copy is `bumpCall_spec`'s inner `have h : …`
block — the standard `abiFrame_spec` conclusion with your frame/vals/
callerPre/callerPost substituted.

### 6.2 Loop leaf — `AbiFrameLoopDemo` (`mulFrame_spec`)

File: `EvmAsm/Rv64/SAsm/AbiFrameLoopDemo.lean`. Invariant + per-iteration
body + one-line loop + one-line wrap:

```lean
def mulInv (inc outPtr : Word) (K : Nat) (n : Nat) : Assertion :=
  (.x8 ↦ᵣ (inc * BitVec.ofNat 64 (K - n))) ** (.x11 ↦ᵣ inc) ** (.x10 ↦ᵣ outPtr)

theorem mulLoopBody_spec … := by … -- 3 instr specs + runBlock

theorem mulLoop_spec (inc outPtr kw : Word) :
    cpsTripleWithin (kw.toNat * (3 + 1) + 1) (0x1018 : Word) (0x1028 : Word) mulCr … := by
  countdown_loop (16 : BitVec 13) (fun n hn => mulLoopBody_spec inc outPtr kw.toNat n hn)

theorem mulFrame_spec … := by
  have hbody : … := by …          -- prefix ; loop ; suffix, framed
  abi_frame (32 : BitVec 12) halign hbody
```

The invariant is the genuine one (`s0 = inc·(K−n)`); a `decide`-away or
vacuous invariant will be rejected in review.

### 6.3 Cross-call on a REAL guest routine — `bnq_set_one`

File: `EvmAsm/Codegen/Programs/Bn254Fq12SetOneSAsm.lean`. This is the
template for tier C. Structure:

1. **Anchors + byte-tie** (byte-transparent — the emitted prog IS the
   flatten, including the concrete guest-linked `jalOff`):

   ```lean
   #guard GuestAddrs.bnq_zero = 0x800305E8
   #guard GuestAddrs.bnq_set_one = 0x80030600
   def setOneBody : List Instr :=
     [ .MV .x8 .x10,
       .JAL .x1 (jalOff GuestAddrs.bnq_zero (GuestAddrs.bnq_set_one + 16)),
       .LI .x5 (1 : Word),
       .SD .x8 .x5 (0 : BitVec 12) ]
   #guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) setOneFrame setOneBody
     = bnqSetOne_prog
   def bnqCr : CodeReq :=
     CodeReq.ofProg (0x800305E8 : Word) (bnqZero_prog ++ bnqSetOne_prog)
   ```

2. **Callee flat contract** `bnqZeroFlat_spec` — a do-while store loop over
   the writable dword region `dwordsIs`, with the genuine zero-prefix
   invariant, closed by `countdownLoopBottom_spec`; conclusion is exactly
   the §5 shape.

3. **The call** inside the body, at call site `A = 0x80030610`:

   ```lean
   have hcallee := bnqZeroFlat_spec ((0x80030610 : Word) + 4) dst v7 vs hlen (by decide)
   have hcall := callWithin_spec (0x80030610 : Word) (0x800305E8 : Word) ret
     (jalOff GuestAddrs.bnq_zero (GuestAddrs.bnq_set_one + 16)) (1 + 48 * (3 + 1) + 1)
     (by decide) (by code_mem) (by pcf) hcallee
   rw [show (0x80030610 : Word) + 4 = (0x80030614 : Word) from by decide] at hcall
   ```

4. **Wrap**: `abi_frame (16 : BitVec 12) halign hbody`. The genuine post:
   `sp`/`ra`/`s0` restored to entry AND
   `dwordsIs dst ((1 : Word) :: List.replicate 47 (0 : Word))` — the FQ12
   at the entry `a0` is ONE.

### 6.4 Anti-example: a thin wrapper blocked by its callee (STOP here)

`header_extract_number` looks like the easiest cross-call port in the tree:
an 8-instruction frame wrapper that calls `rlp_field_to_u64` with a fixed
field index — a perfect `abi_frame` + `frame_call` fit. **It is not
portable yet**, and trying to prove the caller first is wasted work: the
callee `rlp_field_to_u64` is 42 instructions, framed, uses global
`rfu_offset`/`rfu_length` scratch, itself calls `rlp_list_nth_item`, and
has three status exits — it has neither a flat contract nor an adaptable
`Fn.Spec`. The cross-call rule is strictly bottom-up: **when you triage a
wrapper, triage its callees FIRST**; if any callee is missing a contract
and is out of your tier, file/point to a blocker bead (here
`evm-asm-4ch8f.26.7.1`) and stop at that layer. Do not "provisionally
assume" a callee contract — there is no sound way to consume an assumption.

## 7. Byte-tie discipline

**Verified == emitted is non-negotiable.** The `#guard`/`rfl` tie between
your `abiFrameProg …` flatten and the checked-in `<name>_prog` is what
makes the proof about the actual guest bytes.

- **Byte-transparent port** (the common, mechanical case): the tie is
  against the EXISTING `<name>_prog`; the guest image does not change; no
  A/B run is needed; no artifact regeneration is needed.
- **Re-emit drop-in** (tier D): if the emitted code cannot be verified
  as-is (misaligned access, early-exit loop shape, …), the routine is
  re-emitted in verifiable form. That changes guest bytes, and requires
  the full discipline from PR #9975 (`ParentHeaderFrame.lean`): byte-tie
  to the NEW bytes, `scripts/gen-symbol-addresses.py --build`,
  `scripts/check-region-map.sh`, `scripts/check-asm-to-program.sh`
  (fixture update), and **ziskemu/EEST A/B parity vs the old bytes** —
  green AND behaviorally identical. Do not attempt without reading that
  precedent; when in doubt escalate.

## 8. Definition-of-done checklist (run ALL of this before opening a PR)

```bash
# 1. full build (not just your file)
lake build

# 2. axioms: add `#print axioms <yourSpec>` lines at the end of your file,
#    rebuild, and READ the output. It must be EXACTLY
#    [propext, Classical.choice, Quot.sound]
#    — anything else (sorryAx, Lean.ofReduceBool, Lean.trustCompiler) = NOT DONE.
lake build <YourModule> 2>&1 | grep axioms

# 3. gates
bash scripts/check-forbidden-tactics.sh    # no native_decide / bv_decide
bash scripts/check-axioms.sh
bash scripts/check-layering.sh
```

And verify by hand:

- [ ] the `#guard` byte-tie(s) are present and the `rfl` theorem compiles;
- [ ] the postcondition is the routine's **genuine semantics** — not
  `True`, not weakened, not "conservative bail" (a reviewer will diff your
  post against the assembly's actual effect);
- [ ] no `sorry`, no `set_option maxHeartbeats/maxRecDepth` anywhere;
- [ ] module wired in: Codegen port files →
  `EvmAsm/Codegen/Programs/Imports.lean`; core SAsm files →
  `EvmAsm/Rv64/SAsm.lean`. **No `EvmAsm/Progress.lean` registration**
  (Codegen-layer ports are not registry tiers);
- [ ] a bead claimed: `export BEADS_DIR=/home/yoichi-bkp/evm-asm/.beads;
  bd update <bead> --status in_progress` (or `bd create` a child of the
  routine's family bead), and a completion comment before the PR;
- [ ] structured layer untouched: your diff must not modify
  `Ast.lean`/`Vc.lean`/`StmtSound*.lean`/`blockOk` or any existing proof
  file you don't own;
- [ ] don't self-merge.

## 9. Pitfalls & known limits

- **Elaboration limits at scale**: `abi_frame`/the wrappers work at demo
  and small-routine scale; the 84-instruction `parent_header` routine
  times out in the wrapper's automated search and keeps an explicit
  `abiFrame_spec` application. If your `abi_frame` call hits
  `maximum recursion depth` / heartbeat errors, do NOT raise limits
  (forbidden) — escalate.
- **`code_mem` needs concrete data**: symbolic bases/instruction lists
  make the `decide` branches fail. Anchor at literals or `GuestAddrs`
  constants and `#guard`-tie them.
- **Numeral normalization**: single-step specs produce exits like
  `0x100C + 4`; seq-gluing needs syntactic matches — insert
  `rw [show (0x100C : Word) + 4 = (0x1010 : Word) from by decide] at h`
  immediately (every worked example does this).
- **Alignment**: the verified model requires naturally aligned accesses.
  A hand-written `lwu`/`lw` from a possibly-unaligned pointer cannot be
  verified as-is → re-emit territory (tier D).
- **Cross-calls are bottom-up**: never assume a callee; its contract must
  be a proven theorem you instantiate. `x0` note: the loop lemmas carry a
  `(Reg.x0 ↦ᵣ (0 : Word))` atom — include it in your working set.
- **`runBlock` chains single-instruction specs only**; a lifted loop or a
  call composes with `cpsTripleWithin_frameR` +
  `cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp)` —
  copy the chain from `bnqZeroFlat_spec` or `twiceFrame_spec`.
- **Separate semantic constants from address anchors.** When adapting a
  port from a sibling routine, NEVER substitute constants mechanically:
  address literals can embed the size token (a `blq` port was bitten by an
  address ending in `…48` colliding with the 48-dword count). Keep two
  clearly-labeled blocks — the semantic constants (element count, byte
  size, post value) and the address anchors (entry, call site,
  per-instruction addresses derived as entry + 4·k) — and `#guard`-tie
  every anchor to its `GuestAddrs` constant so a stale anchor fails the
  build instead of silently proving a theorem about the wrong address
  (exactly the drift the `#guard`s caught in `Bn254Fq12SetOneSAsm.lean`
  after a guest re-link).
- **Framed empty-core jumps leave a leading `empAssertion`.** `jal x0`
  (and other `empAssertion → empAssertion` specs) framed with `F` produce
  `(empAssertion ** F)`-shaped states; clean up with the
  `sepConj_emp_left'`/`sepConj_emp_right'` equalities (`rw` them, or keep
  the `empAssertion` atom and let `xperm_hyp` match it — both sides must
  then carry the SAME number of `emp` atoms; a count mismatch is the usual
  cause of `xperm: could not find atom … empAssertion`).
- **Genuine post, always.** If you cannot state/prove the routine's real
  semantics, stop and report; a weakened post merged today poisons every
  future composition on top of it.
