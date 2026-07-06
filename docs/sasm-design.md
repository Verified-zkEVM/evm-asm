# SAsm: A Structured Assembly DSL with VC-Generating Verification

Status: design accepted (see "Decisions" below); implementation staged in
milestones. This document is expected to be refined by subsequent commits as
implementation feedback arrives.

## 1. Motivation

The bounded-CPS WP framework (`EvmAsm/Rv64/WP/`, `CPSSpec.lean`) is sound and
composable, but writing and verifying a program with it today costs far more
than it should. The verified RLP withdrawal decoder is the reference data
point: ~58 instructions of program required ~9,500 lines across five files,
dominated by

- hand-built `CodeReq.union` trees and ~92 manual `CodeReq.Disjoint` proofs,
- hand-computed branch/jump offsets (`BEQ x11, x0, 156`) that must be kept in
  sync with block sizes,
- manual composition of `WP.Branch`/`WP.NBranch` exits, one theorem per
  control-flow merge,
- re-stating the full assertion shape (every register atom, every region) at
  every seam.

`run_stateless_guest` (`EvmAsm/Stateless/Entry.lean`) — the intended
verification target — is check-heavy in exactly the way the RLP decoder is:
long chains of format/bounds checks that bail out to failure exits, a few
bounded loops (byte copies, header walks), and calls between routines using
the project's C-like ABI. Verifying it with today's tooling would multiply the
RLP experience by an order of magnitude.

SAsm ("structured assembly") is a DSL layered *on top of* the existing WP
framework that removes each of the costs above by construction:

- **Structure instead of offsets.** Programs are written with `ite`, `when`
  (if-without-else), bounded `while`, and `call`. A flattener computes every
  branch/jump offset and the program's `CodeReq`; disjointness disappears
  because a function's code is one `CodeReq.ofProg` over one contiguous range.
- **One symbolic state instead of N assertion shapes.** Basic blocks operate
  on a fixed *exposed register file*; the DSL derives each block's
  post-state by symbolic execution, so users never write per-block
  register-atom assertions.
- **Pure VCs instead of separation-logic goals.** A VC generator — a plain
  structurally-recursive Lean function, not a tactic — crunches the annotated
  program into a list of *labeled pure propositions*. One generic soundness
  theorem (proved once, by induction on the AST) converts proofs of those VCs
  into the standard `cpsTripleWithin` statement. Proof search never recurses
  over the program, so `maxRecursion`-style failures are avoided by
  construction.

Nothing in the trusted base changes: the final artifact of every SAsm
verification is an ordinary `cpsTripleWithin` about `stepN` over the existing
machine semantics, kernel-checked, closed under the usual three classical
axioms. All proof conventions from `CLAUDE.md` apply (no `native_decide` /
`bv_decide`).

## 2. Decisions (user-confirmed)

Three interface questions were posed and decided 2026-07-01:

1. **VC front-end: tactic with named cases.** A `vcgen` tactic applies the
   generic soundness theorem and splits the VC list into one *named* goal per
   verification condition. Each goal is pure (registers-as-values, `Nat`/
   `BitVec` arithmetic, list facts); the case name encodes the program path
   (e.g. `check_empty_input`, `copy_loop.inv_step`). Failure feedback for the
   agentic workflow is precise: the leftover named goals *are* the report.
2. **Block leaves: raw instruction lists.** Basic blocks are `List Instr`
   exactly as everywhere else in the repo; the DSL adds structure around them
   and derives their semantics by symbolic execution. This reuses the
   instruction set, the codegen pipeline, and auditability of the emitted
   assembly.
3. **Annotations: inline in the AST.** Loop invariants, bounds, and optional
   mid-conditions are nodes/fields of the program term itself; a function's
   pre/post live in the `Fn` record next to its body.

## 3. Architecture

```
        user writes                        SAsm derives
  ┌───────────────────────┐      ┌────────────────────────────────┐
  │ Fn record:            │      │ Fn.program  : Program (flat)   │
  │  pre/post (pure, over │ ───▶ │ Fn.codeReq  : CodeReq.ofProg   │
  │  exposed reg file)    │      │ Fn.steps    : Nat (step bound) │
  │  regions (spatial)    │      │ Fn.vcs      : List VC (labeled │
  │  body : Stmt          │      │               pure Props)      │
  └───────────────────────┘      └────────────────────────────────┘
                                              │
                     Fn.sound : VCs.Hold f.vcs → Fn.Spec f base
                                              │
                                              ▼
                    cpsTripleWithin f.steps base exit f.codeReq P Q
```

Layer by layer, bottom-up:

### 3.1 Exposed register file (`SAsm/RegFile.lean`)

A fixed set of registers is *exposed* to SAsm basic blocks:

```
exposed := [x5, x6, x7, x28, x29, x30, x31,      -- t0–t6 (scratch)
            x10, x11, x12, x13, x14, x15, x16, x17]  -- a0–a7 (args/returns)
```

`x0` is handled specially (always 0). `x1` (ra), `x2` (sp), and the s-registers
are *not* exposed: `ra`/`sp` are owned by the call machinery (§3.6), and
s-registers are left to the frame (a leaf SAsm function neither reads nor
writes them, so the built-in frame rule of `cpsTripleWithin` preserves them
for free).

```lean
def RegFile := ExposedReg → Word          -- ExposedReg: subtype/enum of the 15
def RegFile.get  : RegFile → Reg → Word   -- x0 ↦ 0; non-exposed: junk (unused)
def RegFile.set  : RegFile → Reg → Word → RegFile

/-- Ownership of exactly the exposed registers, with values `rf`. -/
def regFileIs (rf : RegFile) : Assertion :=
  fun h => h = PartialState.ofRegFile rf     -- pc-free by construction
```

Defining `regFileIs` as a single `PartialState` equality (like
`regIs`/`memIs`) rather than a 15-way `**` chain is deliberate: block
soundness then needs *one* generic per-instruction lemma instead of
permutation reasoning over a big separating conjunction, and `xperm`-style
atom-count blowups (see `build_perf_findings`) never occur, because to the
sep-logic layer the whole register file is one atom.

Bridging lemmas connect `regFileIs rf` with the atom form
(`(.x5 ↦ᵣ rf .x5) ** …`) in both directions, so SAsm specs compose with
existing hand-written specs at function boundaries.

### 3.2 The AST (`SAsm/Ast.lean`)

```lean
/-- Branch conditions available to structured control flow: exactly the
    RV64 conditional branches, over exposed registers. -/
inductive Cond where
  | beq | bne | blt | bge | bltu | bgeu   -- each carries (rs1 rs2 : Reg)

def Cond.holds : Cond → RegFile → Prop    -- e.g. bltu: BitVec.ult (rf rs1) (rf rs2)
def Cond.neg   : Cond → Cond              -- beq↔bne, blt↔bge, bltu↔bgeu
def Cond.toInstr : Cond → BitVec 13 → Instr

inductive Stmt where
  /-- Straight-line block of raw instructions from the supported subset. -/
  | block  (label : String) (instrs : List Instr)
  | seq    (a b : Stmt)                                           -- a ;; b
  | ite    (label : String) (c : Cond) (thn els : Stmt)
  | when   (label : String) (c : Cond) (body : Stmt)              -- if, no else
  /-- Optional mid-condition: no code, cuts the reachable-state set. -/
  | assert (label : String) (P : RegFile → Prop)
  /-- Bounded loop: body runs while `c` holds, at most `fuel` iterations.
      `inv i` must hold on entry to the i-th header evaluation. -/
  | while  (label : String) (c : Cond) (fuel : Nat)
           (inv : Nat → RegFile → Prop) (body : Stmt)
  /-- Direct call to a routine with a registered interface (§3.6). -/
  | call   (label : String) (f : FnHandle)
```

Notes:

- Labels name VCs; they need not be globally unique — the VC generator
  prefixes them with the path (e.g. `outer.body.check_len`).
- `inv`'s `Nat` index is the iteration counter, matching `WP.loopNatCert`.
  Invariants over other ghost data (decoded prefixes, offsets) use ambient
  Lean binders: an SAsm function is defined inside ordinary `variable`s /
  parameters, so `inv`, `assert`, `pre`, `post` may all mention them freely.
- Ghost-state generality: because annotations are arbitrary
  `RegFile → Prop` over ambient binders, the DSL is not RLP-specific;
  any effect expressible in the separation logic can appear in the spatial
  part (§3.3) and any functional property in the pure part.

Sequencing sugar: `a ;;; b` (or reuse a `do`-like macro layer later —
cosmetic, out of scope for v1).

### 3.3 Spatial state: regions (`SAsm/Region.lean`)

Check-heavy code (RLP, SSZ) reads from byte buffers and writes results.
SAsm models spatial state as a list of *regions* owned by the function:

```lean
structure Region where
  base  : Word
  bytes : List Byte          -- current contents
  mode  : Region.Mode        -- .ro (read-only) or .rw

def regionsAssert : List Region → Assertion   -- ⋆ of bytesRegion-style atoms
```

- v1 (Milestones 1–3): `.ro` regions only. Loads (`LBU`/`LHU`/`LWU`/`LD`)
  from an in-range address of a `.ro` region symbolically evaluate to the
  known byte(s); the in-range condition becomes a labeled VC. The regions
  assertion is invariant across the function, so the sep-logic side never
  changes shape — this already covers the *checking* half of RLP decoding.
- v2 (Milestone 5b-2, **landed shape**): one read-only `Region` (base +
  ghost bytes) plus one writable `RwRegion` (base + length; the *contents*
  are part of the symbolic state).  `Reach` is
  `RegFile → List Byte → Prop` — register file plus the writable region's
  current bytes; `asrtOf rw reach` existentially bundles both with the
  byte count pinned to `rw.len`.  Loads route by address: an access fully
  inside the writable window reads the symbolic contents, everything else
  reads the read-only region (the per-load VC follows the same split).
  Overlapping regions need no side condition — the separation conjunction
  makes them unsatisfiable.  Stores (to the writable region only) update
  the symbolic bytes via `setBytes`.
- Other effects (hints, publicValues, …) are future extensions at
  the same seam: enlarge `SymState` and the per-leaf soundness lemmas;
  the structural rules (§3.5) do not change.

### 3.3.1 ZisK accelerator semantics (`Rv64/ZiskAccel.lean`, design decisions)

The guest's hashing and crypto kernels call ZisK precompiles through raw
`csrs <id>, <reg>` words (`.4byte 0x80052073` etc.); bead evm-asm-4ch8f.1
models them (machine level, below SAsm):

- **Concrete, not parametrized.**  `Instr.CSRS csr rs1` executes the
  actual mathematical function per CSR id — Keccak-f[1600], the SHA-256
  compression, exact-intermediate `(a*b + c) mod m` — rather than an
  axiomatized accelerator contract.  Rationale: (1) evm-asm carries
  *software* implementations of several hashes (RIPEMD-160, SHA-256
  wrapper, P-256 over Arith256Mod), and their proofs must meet the
  accelerator path at the same concrete function; (2) an axiomatized
  contract widens the trusted base beyond the three classical axioms;
  (3) concrete permutations admit in-repo kernel-checked known-answer
  tests (`keccakF_kat_empty`, `sha256Compress_kat_empty`, pinned to
  `keccak256("")`/`sha256("")`).  What a parametrized model would buy —
  insulation from ziskemu version drift in operand packing — is instead
  handled by pinning the layouts to the probe results
  (`Codegen/Programs/HashProbes.lean`) and re-validating via EEST runs.
- **Modeled ids**: `0x800` Keccakf (25-lane LE state, in place),
  `0x802` Arith256Mod (`[a*, b*, c*, module*, d*]`, 4 LE u64 limbs each),
  `0x805` Sha256f (`[state*, input*]`, LE-u32-in-u64 packing),
  `0x80B` Arith384Mod (6-limb Arith256Mod sibling), `0x819` Blake2bRound
  (`[sigmaIdx, state*, input*]`, one RFC 7693 round on the 16-word
  working vector), `0x803`/`0x804` Secp256k1Add/Dbl (affine chord/
  tangent over concrete field arithmetic, fuel-indexed kernel-reducible
  `powMod` inversion; degenerate inputs trap), `0x806`–`0x80A` BN254
  curve+Fp2, `0x80C`–`0x810` BLS12-381 curve+Fp2 (same generic helpers
  at (modulus, limbs) = (bn254P, 4) / (bls12P, 6); complex ops are
  componentwise mod p with `u² = −1`).  This closes every accelerator id
  the guest emits.  `execCsrs` is definitionally ONE `writeWords` (a
  pure `csrsWrite` computes target and payload), so state-projection
  lemmas are branch-count-independent.
- **Traps, not no-ops.**  `step` requires `csrsValid`: every operand dword
  a valid access and (Arith256Mod) a nonzero modulus; an UNMODELED CSR id
  always traps.  A verified triple over code containing a `csrs` therefore
  cannot silently skip the accelerator — the proof obligation is exactly
  the operand-block validity.
- **The ECALL surfaces stay as they are**: SP1-convention HALT/WRITE/
  read_input remain on `ECALL` in `step`; ZisK accelerators are csrs-only.
- **SAsm exposure is deliberately deferred** to the consuming beads
  (.17 keccak bridge, .18 sha256): `blockOk` rejects `CSRS` inside blocks
  today; the bridge beads decide between a new block-leaf classification
  (`accelSem`, mirroring `storeSem` with a multi-dword footprint) or a
  `Stmt`-level node.  The machine-level `step_csrs`/`step_csrs_trap`
  lemmas are the composition points either way.

### 3.4 Block symbolic execution (`SAsm/Sym.lean`)

Two plain functions over the supported instruction subset:

```lean
/-- Forward symbolic execution of a straight-line block. -/
def execBlock (regions : List Region) : RegFile → List Instr → RegFile

/-- Side conditions collected along the way (load in-range, alignment,
    instruction supported). Pure, decidable-or-arithmetic shaped. -/
def blockVCs (regions : List Region) : RegFile → List Instr → Prop
```

Supported subset in v1: ALU reg/imm ops (`ADD(I)(W)`, `SUB`, `AND(I)`,
`OR(I)`, `XOR(I)`, `SLL(I)`, `SRL(I)`, `SRA(I)`, `SLT(I)(U)`), constants
(`LI`, `LUI`, `MV`, `NOP`), `MUL`-family, and `.ro` loads. Everything else
(stores, `ECALL`, …) is rejected by `blockVCs` with a `False`-shaped VC that
names the offending instruction — the failure mode is a readable goal, not a
stuck tactic.

The single enabling soundness lemma, proven once, generically:

```lean
theorem execBlock_sound :
    blockVCs regions rf instrs →
    cpsTripleWithin instrs.length base (base + 4 * instrs.length)
      (CodeReq.ofProg base instrs)
      (regFileIs rf ** regionsAssert regions)
      (regFileIs (execBlock regions rf instrs) ** regionsAssert regions)
```

by induction on `instrs`, with one lemma per supported instruction shape
(mirroring `generic_1reg_spec_within` but stated against `regFileIs`).

### 3.5 VC generation and soundness (`SAsm/Vcgen.lean`, `SAsm/Sound.lean`)

The core is a strongest-postcondition–style generator over the pure
abstraction. `Reach := RegFile → Prop` is the abstract reachable-state set
(v2: over `SymState`).

```lean
structure VC where
  label : String
  prop  : Prop

/-- (VCs of this statement, reachable set at its exit). Structurally
    recursive — unfolds in time linear in the AST, independent of proof
    search. -/
def Stmt.spgen (regions) : Stmt → (reach : Reach) → List VC × Reach
  | block l is  => ([⟨l ++ ".ok", ∀ rf, reach rf → blockVCs regions rf is⟩],
                    fun rf' => ∃ rf, reach rf ∧ rf' = execBlock regions rf is)
  | seq a b     => let (v₁, r₁) := a.spgen reach
                   let (v₂, r₂) := b.spgen r₁
                   (v₁ ++ v₂, r₂)
  | ite l c t e => let (v₁, r₁) := t.spgen (fun rf => reach rf ∧ c.holds rf)
                   let (v₂, r₂) := e.spgen (fun rf => reach rf ∧ ¬ c.holds rf)
                   (v₁ ++ v₂, fun rf => r₁ rf ∨ r₂ rf)
  | when l c b  => -- ite with skip else-branch
  | assert l P  => ([⟨l, ∀ rf, reach rf → P rf⟩],
                    fun rf => reach rf ∧ P rf)          -- cut strengthens
  | while l c n inv b =>
      let (vb, rb) := b.spgen (fun rf => ∃ i < n, inv i rf ∧ c.holds rf)
      ([⟨l ++ ".inv_init⟩", ∀ rf, reach rf → inv 0 rf⟩,
        ⟨l ++ ".inv_step",  ∀ i < n, ∀ rf', rb… → inv (i+1) rf'⟩,   -- see below
        ⟨l ++ ".fuel_exhausted", ∀ rf, inv n rf → ¬ c.holds rf⟩] ++ vb,
       fun rf => ∃ i ≤ n, inv i rf ∧ ¬ c.holds rf)
  | call l f    => ([⟨l ++ ".pre", ∀ rf, reach rf → f.pre rf⟩],
                    fun rf' => ∃ rf, reach rf ∧ f.postRel rf rf')
```

(The `inv_step` VC is generated with the body's reach threaded per iteration
index `i`; the sketch above elides the index plumbing that the implementation
carries through `spgen`.)

The generic soundness theorem, proven **once** by structural induction on
`Stmt`, maps each constructor onto the existing WP combinators:

| AST node | WP machinery used |
|---|---|
| `block`  | `execBlock_sound` (§3.4) |
| `seq`    | `WP.Triple.seq` / `cpsTripleWithin_seq_same_cr` |
| `ite`/`when` | `generic_b*_spec_within` + `WP.Branch.join` |
| `assert` | `WP.Triple.refl` (pure strengthening, 0 instructions) |
| `while`  | `WP.loopNatCert` + `loopNatCert_sound` |
| `call`   | `cpsCallWithin` (§3.6) |

```lean
theorem Stmt.spgen_sound (s : Stmt) (reach : Reach) :
    VCs.Hold (s.spgen regions reach).1 →
    cpsTripleWithin (s.steps) base (base + 4 * s.size)
      (CodeReq.ofProg base (s.flatten …))
      (fun h => ∃ rf, (regFileIs rf ** regionsAssert regions) h ∧ reach rf)
      (fun h => ∃ rf, (regFileIs rf ** regionsAssert regions) h ∧
                      (s.spgen regions reach).2 rf)
```

Everything inside one function shares a *single* `CodeReq.ofProg base prog`;
sub-statements' triples are stated against slices and lifted with
`Triple.extendCode` + `CodeReq.ofProg_append` monotonicity — no
`Disjoint` obligations reach the user, ever. The `ite`/`when`/`while` branch
offsets are synthesized by the flattener (§3.7) and their 13/21-bit range
side-conditions are emitted as VCs that `decide` closes (label suffix
`.ofs`); the `vcgen` tactic discharges these automatically.

Step bound: `Stmt.steps` is computed structurally (`while` uses
`WP.loopBound`); the final `cpsTripleWithin` carries this exact bound, which
is what makes the DSL a *total-correctness* Hoare logic with a max
instruction count, per the project's convention.

### 3.6 Functions and the C-like interface (`SAsm/Fn.lean`)

```lean
structure Fn where
  name    : String
  regions : List Region := []
  pre     : RegFile → Prop                 -- over a0–a7 typically
  post    : RegFile → RegFile → Prop       -- entry rf ↝ exit rf (a0/a1 results)
  body    : Stmt

/-- Everything a caller needs; deliberately forgets the body. -/
structure FnHandle where
  entry   : Word
  code    : CodeReq
  nSteps  : Nat
  regions : List Region
  pre     : RegFile → Prop
  postRel : RegFile → RegFile → Prop
  sound   : ∀ ret rf, ret &&& ~~~(1:Word) = ret → pre rf →
    cpsTripleWithin nSteps entry ret code
      ((.x1 ↦ᵣ ret) ** regFileIs rf ** regionsAssert regions)
      (fun h => ∃ rf', ((.x1 ↦ᵣ ret) ** regFileIs rf' **
                         regionsAssert regions) h ∧ postRel rf rf')
```

- The ABI is the project's convention (`Stateless/MemoryLayout.lean`):
  arguments and returns in a0–a7/a0–a1, t-registers clobbered freely
  (`postRel` simply doesn't constrain them), s-registers/sp untouched by
  leaf functions (framed).
- **Calling a DSL function from another DSL function is one AST node**:
  `Stmt.call l f.handle`. The generator emits a single `.pre` VC and
  continues with `postRel`-shaped reach. `Fn.handle : verified Fn → FnHandle`
  is a projection — its `sound` field *is* the function's SAsm spec
  instantiated at `ret`, since SAsm functions end in `JALR x0, x1, 0` and are
  verified against a universally-quantified return address.
- Hand-verified (non-SAsm) routines join the same ecosystem by packaging
  their existing `cpsTripleWithin` spec as a `FnHandle` (adapter lemmas
  bridge atom-form assertions to `regFileIs`, §3.1).
- Non-leaf functions (bodies containing `call`) need `ra` saved.
  `Fn.toHandleR` (`SAsm/RaSpill.lean`) packages a caller verified via
  `soundR` as a callee: the emitted code is
  `SD rs, x1, sofs ; body ; LD x1, rs, sofs ; JALR x0, x1, 0`, where the
  spill slot is a dword of the function's `.rw` region and `rs` is an
  exposed register that the pre pins to its address.  The return address is
  threaded through the body as a ghost word — the packaging consumes a
  family of `SpecR`s indexed by the spilled value, whose pre/post record
  that the slot holds it, so slot preservation is the caller's own `.post`
  VC.  The `ExamplesVc` two-level tree
  (`topFn` → `callerRHandle` → `leafHandle`) exercises the full shape.
- **Per-frame writable sub-regions** (`SAsm/HandleWiden.lean`).
  `CalleesIn` requires a callee to declare the caller's own `.rw` region,
  which — taken alone — forces a whole call tree to share one region and
  every callee contract to thread the caller's private state (spill slots)
  as ghost data.  `FnHandle.widenRw` removes the coupling: a callee
  verified against its own *window* (a dword-aligned, dword-multiple
  sub-range of the caller's region) is repackaged over the full region
  with the outside bytes `preB`/`sufB` framed across the call — the
  widened post pins them to their entry values by construction, so the
  caller's slots survive calls without callee cooperation.  The caller
  instantiates `preB`/`sufB` per call site with its own ghost values
  (e.g. `dwordBytes v` for the spilled `ra`).  The underlying frame seam
  is `bytesRegion_append` (split a byte region at a dword boundary).
  `WidenDemo` replays the ra-spill two-level tree with the leaf owning
  only its 8-byte window; register-preservation conventions across calls
  are §3.6.2 (`SAsm/FrameConv.lean`).
- **Read-only sub-slices** (`FnHandle.widenRo`, same file): the `.ro`
  analogue — a callee verified against its own slice of a larger
  read-only buffer is repackaged over the caller's full region, pre/post
  unchanged (ro contents live in the region descriptor).  `RoWidenDemo`
  shows the intended shape for named-arena addressing: ONE leaf routine
  (one code copy at one entry), its contract instantiated per call site
  at a different slice, the caller materializing each slice pointer with
  `LI` — the SAsm rendering of `la`-per-arena.

### 3.6.1 Named regions and `la` addressing (design decisions)

How the guest's many named `.data` arenas map onto SAsm, decided with
the first widening adapters (bead evm-asm-4ch8f.2):

1. **Contiguous named slices of one buffer** (SSZ input sections, packed
   arenas): the caller declares one region; callees declare only their
   slice and are widened per call site (`widenRo`/`widenRw`).  These
   adapters ARE the per-region frame conditions — no soundness-induction
   or AST change, framing at the `bytesRegion_append` seam.
2. **Genuinely disjoint arenas** (e.g. an SSZ slice plus a `.data` table
   at `0xa3000000`): the primary region/rw stay as-is; additional arenas
   ride in the ambient assertion `A` as `bytesRegion` conjuncts, accessed
   by blocks through `.blockAt` focus windows and framed across calls by
   `FnHandle.frameA`.  A function's contract thus lists exactly the
   arenas it touches: primary region + rw + the `A`-conjuncts of its pre.
   This is also the sanctioned **multiple-writable-regions** design
   (bead evm-asm-4ch8f.67): a routine writing two+ independent writable
   pointers (result buffer + length/count dword, the `swd_minimal_copy`
   shape) keeps region 1 as its primary `rw` and writes each further
   region through a `blockAt` at that region's pointer — assertion-atom
   store routing at block granularity, with disjointness structural
   (`**`) rather than an arithmetic side condition.  Decision record +
   worked two-region function: `SAsm/MultiRw.lean`; recipe:
   docs/sasm-howto.md §6 ("Multiple writable regions").
3. **Symbol (`la`) addressing**: guest symbol addresses are concrete at
   build time (`.data` is linker-pinned), so SAsm code materializes them
   with `LI` (64-bit pseudo already in `Instr`) and specs pin pointer
   registers to named `Word` constants; region bases may equally be
   ambient Lean binders for position-independent contracts (see
   `roLeafFn b xs`).  The authoritative named `def <sym>Addr : Word`
   table plus pairwise-disjointness facts is the memory-layout
   formalization's deliverable (bead evm-asm-4ch8f.6); SAsm consumes
   those names, it does not define them.

### 3.6.2 Register preservation and frame layout (design decisions)

How values survive calls and where frames live (bead evm-asm-4ch8f.3,
`SAsm/FrameConv.lean`):

1. **Exposed registers (t0–t6, a0–a7) are caller-saved.**  `Stmt.sp` for
   a `.call` replaces the reachable set by the callee's postcondition —
   the callee owns the whole exposed file, so any register its post does
   not mention is forgotten.  Two conventions keep a value live:
   - *contract pinning* (`Reach.pin r v`): when the callee provably does
     not touch `r`, its contract family carries the entry value `v` as a
     ghost through pre AND post; the callee's own `.post` VC proves the
     preservation and the caller gets it for free — zero runtime cost
     (`PinDemo`: `w` survives in `x15` across a call and is used after);
   - *spill/reload*: the caller stores the value into a private dword of
     its own frame window — outside the callee's `widenRw` window, so
     the widened post preserves the slot by construction — and reloads
     after the call (`SpillDemo`: `w` survives a callee that clobbers
     `x15`).  Pointers are never spilled: they are re-materialized with
     `LI` from the static layout (§3.6.1), which keeps reload blocks
     self-contained.
2. **s-registers (and `sp`/`gp`/`tp`) need no machinery.**  They are
   outside the exposed set: `blockOk` rejects any read or write, so a
   verified SAsm routine can never clobber them.  They only matter at
   boundaries with unverified raw asm, where the boundary spec owns them.
3. **Frames are static windows; no dynamic `addi sp`.**  Each verified
   routine gets a fixed dword-aligned window of the stack arena, assigned
   by the global memory layout (bead evm-asm-4ch8f.6) and carved per call
   edge by `FnHandle.widenRw`; `ra` spill slots live in the routine's own
   window (`Fn.toHandleR`, slot dword `k` of `.rw`, first dword by
   convention).  The guest's existing `addi sp`-style frames are
   *replaced* by this convention, not modeled — sound because the
   verified call graph is a finite static tree, so total stack need is
   known at layout time.  Dynamically-deep recursion (the EVM
   interpreter's call depth) does not stack-allocate: it goes through the
   data-indexed EVM frame arena (beads evm-asm-4ch8f.5/.56).

### 3.6.3 Indirect calls (`Stmt.callReg`, design decisions)

The guest dispatches through function pointers in three places: the
256-entry `opcode_handlers` jump table, `tx_type_dispatch`, and
runtime-armed backends (`ecrecover_backend_ptr`).  All of them reduce to
one primitive (bead evm-asm-4ch8f.4):

- **`Stmt.callReg lbl rs handles`** emits a single `jalr ra, rs, 0` and
  carries a *finite table* of candidate callees.  Its one `.pre` VC
  demands that every reachable state pin the (exposed) register to the
  entry address of some handle whose precondition holds:
  `∃ h ∈ handles, rf.get rs = h.entry ∧ h.pre rf ws A`.  The strongest
  postcondition is the disjunction `∃ h ∈ handles, h.post rf ws A`; the
  step bound is `1 +` the folded maximum of the handles' bounds.
  Soundness (the `callReg` case of `Stmt.soundR`) splits the symbolic
  state, picks the handle the `.pre` VC names, steps the `jalr`
  (`jalr_call_spec_within`, which reads the target out of `regFileIs`
  and drops the return address into the owned `ra`), and runs that
  handle's contract — no disjointness side conditions, since both the
  jump and the callee code live in the ambient `cr`.
- **Table loads are not a new primitive.**  A dispatch table in `.data`
  is a read-only region of little-endian dword entries; the load
  `ld rs, 8*i(table)` is ordinary block machinery, and its `.post`
  relates `rf.get rs` to `Region.dwordAt` — exactly what the `.pre` VC
  of the following `callReg` consumes.  Runtime-armed pointers live in a
  `rw` dword instead; same shape.
- **Correlation** (knowing WHICH handler ran): the bare disjunction
  loses it, deliberately.  Callers that need it instantiate the handles'
  ghost contracts per call site — e.g. handler `i`'s instantiated post
  can pin the dispatch index or its distinguishing effect — the same
  per-call-site instantiation used for regions (`RoWidenDemo`) and
  saved registers (§3.6.2).  For the 256-entry opcode table this is one
  handle family indexed by the opcode byte.
- **Address side conditions** (`callsOk`): the return address `pc + 4`
  is aligned and every table entry is a `jalr` fixed point
  (`entry &&& ~1 = entry`) — decidable per concrete layout.  `offsetsOk`
  additionally requires `rs` exposed.  Tail calls (`jalr x0`) remain
  future work; they need a different contract shape (the callee returns
  to the CALLER's caller), not just a new emitter.

`CallRegDemo` exercises the construct end-to-end: two verified handlers,
a caller that selects an entry address on a runtime condition and
dispatches through `x28`, and a proof that the merged postcondition
holds.

### 3.7 Flattening (`SAsm/Flatten.lean`)

```lean
def Stmt.size    : Stmt → Nat            -- instructions incl. synthesized ones
def Stmt.flatten : Word → Stmt → Program -- addr-aware; resolves all offsets
def Fn.program (f : Fn) (base : Word) : Program := f.body.flatten base ++ [JALR x0 x1 0]
```

Layouts (sizes in instructions):

| node | emitted code | size |
|---|---|---|
| `block _ is` | `is` | `is.length` |
| `ite c t e`  | `B¬c → Lelse` · `t` · `J → Lend` · `e` | `t.size + e.size + 2` |
| `when c b`   | `B¬c → Lend` · `b` | `b.size + 1` |
| `while c n _ b` | `Lhdr: B¬c → Lend` · `b` · `J → Lhdr` | `b.size + 2` |
| `call _ f`   | `JAL x1, (f.entry − pc)` | `1` |
| `callReg _ rs hs` | `JALR x1, rs, 0` | `1` |
| `assert`     | (nothing) | `0` |

`#eval`-able: flattened programs plug directly into the existing codegen
`BuildUnit` pipeline, so a verified SAsm routine ships in the same ELF as
today's hand-written programs.

### 3.8 The `vcgen` tactic (`SAsm/Tactic.lean`)

User experience (decided interface):

```lean
theorem memcpy_spec (n : Nat) (xs : List Byte) (base src dst : Word) … :
    (memcpy n xs …).Spec base := by
  vcgen                    -- applies Fn.sound, computes+splits the VC list
  case init               => omega
  case copy.inv_init      => simp
  case copy.inv_step      => intro i hi rf h; …
  case copy.fuel_exhausted=> omega
  case post               => intro rf' h; simpa using h
```

Implementation constraints (robustness / recursion-safety):

- `vcgen` does exactly three things: `apply Fn.sound`, normalize the
  `f.vcs` list by `simp only` with the generator's equation lemmas
  (structural, linear in AST size — no search), then split
  `VCs.Hold (vc₁ :: …)` into named goals, tagging each with its label
  string. It attempts `decide` only on `.ofs`/`.ok`-shaped bookkeeping VCs.
- No recursion over proofs of previous goals; each VC is independent.
  Simp recursion depth is bounded by AST depth (≈ nesting level, single
  digits in practice), never by instruction count or fuel.
- On failure the tactic *names what's missing*: an unsupported instruction
  surfaces as a `False`-conclusion VC labeled with the block and the
  instruction; a missing annotation surfaces as an unprovable `inv_step`
  with the loop label. `vcgen?` (diagnostic variant) prints the VC report
  (label + statement, ✓/✗ after the default pass) without leaving goals,
  for the agentic explore loop.

### 3.9 Phase ownership of aliased arenas (`SAsm/PhaseSplit.lean`, `Codegen/CallFramePhase.lean`)

The guest has exactly one intentional physical aliasing:
`call_frame_arena` (~164 MiB, the Phase-D EVM call-frame overlay) coalesces
seven execution-dead Phase-H arenas into its front
(`RegionMap.dataUnionChildren`; `docs/call-frame-memory-layout.md` §5).
Framing the arena and a coalesced child as two separate regions in one
ambient would be **unsound** (`**` would claim disjoint ownership of the
same bytes), and until this section the no-corruption argument was prose.

The model (bead `evm-asm-4ch8f.6`, hard half):

- **One resource, many tilings.** `anyBytes base n` owns `n` bytes with
  *unspecified contents*.  `anyBytes_add`/`anyBytes_eq_anyTiles` prove a
  havoc'd range equal to any contiguous dword-aligned tiling of itself.
  `CallFramePhase.phaseD_eq_phaseH` instantiates this on the audited union
  inventory: the whole-arena view (`phaseDView`) and the
  seven-children-plus-pad view (`phaseHView`) are the *same assertion*.
- **Transitions forget contents.** A phase transition is one rewrite across
  that equality, entered by weakening concrete buffers through
  `bytesRegion_anyBytes` (`phaseH_to_phaseD` packages the seven-buffer
  handoff).  `anyBytes` carries ownership and length, nothing else — so a
  later phase provably cannot depend on what an earlier phase left in the
  shared bytes, and a stale reader after re-partition receives havoc'd
  buffers, not its old data.  The failure mode the prose worried about is
  structurally unexpressible in a composed proof that frames the arena
  through these views.
- **Consumer obligation.** `cpsTripleWithin_anyBytes_pre`: a triple whose
  precondition owns a havoc'd range must be proven *for every possible
  contents* (demo in `PhaseSplit.lean`: an `LBU` from `anyBytes` admits
  only an existential postcondition).
- **Who uses what.** Phase-H routines (`.41`–`.48`) frame individual child
  ranges (`phaseHView_children` names each child at its audited offset);
  Phase-D dispatch (`.49`, `.56`) frames `phaseDView`; the `block_verdict`
  composition (`.61`) performs the single H→D rewrite at the dispatch
  boundary.  The arena base stays a parameter — the model is
  link-layout-independent; `RegionMap.callFrameArenaBase` pins this build.

What the model does **not** decide: *when* the guest transitions — that
Phase H truly stops touching the children before dispatch is what the
per-routine triples + the composition prove (a Phase-H routine cannot be
composed after the rewrite, because the child views it frames against no
longer exist in the ambient).

### 3.10 Loops at guest scale: data-dependent fuel and nested loops (design decisions)

The guest's loops are input-length-bounded (RLP walks, header chains
≤ 256, BAL scans ≤ 100 k items) and nested (per-account → per-slot →
per-tuple).  Two questions were settled here (bead `evm-asm-4ch8f.5`;
demos in `SAsm/LoopFuelDemo.lean`, bridge lemmas in `SAsm/LoopFuel.lean`):

**1. Runtime-data-dependent iteration counts need no new mechanism.**
The pattern (the *static-cap idiom*, `rlpSkipFn`/`capScanFn`):

- `fuel := cap`, a static worst-case literal (`256`, `100000`).  The
  verified step budget `WP.loopBound 1 (body.steps+1) 1 cap` stays a
  closed `Nat` expression, which is what `cpsTripleWithin` and handle
  packaging want.
- The *exit* is the runtime compare of a counter register against a
  limit register loaded from the input (`.bltu ctr lim`).  Because the
  block engine is deterministic over the ghost region bytes, the loaded
  limit **is** a ghost expression (`(bs.getD 0 0).zeroExtend 64`,
  `packBytes (bs.take 8)`), so the invariant can tie both registers:
  `rf.get ctr = ofNat i ∧ rf.get lim = <decoded ghost> ∧ i ≤ n`.
- The `exhausted` VC is where the cap binds the runtime count: at
  `i = cap` the invariant gives `cap ≤ n`, and `n ≤ cap` — a
  **precondition on the decoded input** (a spec-theorem hypothesis, or
  free from the load width when the count is a single byte) — forces
  `i = n = cap`, where the compare fails.  A wrong cap is not a
  soundness hole; it is an unprovable `exhausted` goal.
- Pure ghost preconditions (`n ≤ cap`, `8 + n ≤ bs.length`) do **not**
  flow into loop-body VCs through `sp` (the loop forgets the entry
  reach) — state them as hypotheses of the spec theorem, where every VC
  goal sees them, rather than in `Fn.pre`.

Exact ghost fuel (`fuel := t0.lDepth`, TreeDemo) remains the right shape
when the count is structural; the static cap is for counts the spec
author only knows an upper bound for.  Rejected alternative: a fuel
*expression* evaluated from registers at runtime — it would make
`Stmt.steps` state-dependent and break the closed step budget of
`cpsTripleWithin` for no expressive gain over the cap idiom.

**2. Nested loops need an AST extension: `Stmt.whileS`.**  The
counter-register bridge alone is *insufficient* for nesting.  The
`while` exit `sp` is `(∃ i ≤ fuel, inv i) ∧ ¬cond` — it **discards the
entry reach**, so in the outer loop's `inv_step` every correlation
between the quantified outer index `i` and the machine state is severed
by an inner loop: the inner invariant cannot mention `i` (it is fixed in
the AST, and the outer index is not a binder of the enclosing `def`),
and no state-only invariant can re-derive it (a pure assertion cannot
injectively encode a `Nat`, and `⌜x5 still holds its entry value⌝` is
not expressible without naming the entry state).  This is the classic
limitation solved by the loop rule with *logical variables*:

```lean
| «whileS» (label : String) (c : Cond) (fuel : Nat)
    (inv : RegFile → List (BitVec 8) → Assertion →   -- the entry snapshot
      Nat → RegFile → List (BitVec 8) → Assertion → Prop)
    (body : Stmt)
```

`inv rf₀ ws₀ A₀ i` is the invariant at header-evaluation `i` for the
loop *entered at* `(rf₀, ws₀, A₀)`.  Same emitted code, same three VCs
as `while`, with the snapshot universally quantified — and constrained
by the entry reach, so entry facts are usable — in `inv_step` and
`exhausted`, and existentially recorded in the exit `sp`:

```
inv_init   : reach rf ws A → inv rf ws A 0 rf ws A
inv_step   : reach rf₀ ws₀ A₀ → i < fuel →
             sp body (inv rf₀ ws₀ A₀ i ∧ cond) ⊆ inv rf₀ ws₀ A₀ (i+1)
exhausted  : reach rf₀ ws₀ A₀ → inv rf₀ ws₀ A₀ fuel rf ws A → ¬cond
sp (exit)  : ∃ rf₀ ws₀ A₀, reach rf₀ ws₀ A₀
               ∧ (∃ i ≤ fuel, inv rf₀ ws₀ A₀ i) ∧ ¬cond
```

The nested pattern (`gridScanFn`): the outer loop is a plain `while`
holding its index in a counter register (`x5`); the *inner* loop is a
`whileS` whose invariant pins the outer state to the snapshot
(`rf.get .x5 = rf₀.get .x5`, row pointer relative to `rf₀.get .x11`).
The outer `inv_step` then closes the chain: its entry gives
`rf₀.get .x5 = ofNat i` (the snapshot is reach-constrained), the inner
invariant transports it to the exit state, and the outer index ties
re-establish.  The snapshot also carries `ws₀`/`A₀`, so "the inner loop
leaves the window/ambient alone" is one equation instead of a
re-derivation.

Soundness (`Stmt.sound`/`Stmt.soundR`, `whileS` cases): fix the entry
state first with `cpsTripleWithin_exists_pre_M`(`_frame`), then the
entry-instantiated family `inv rf₀ ws₀ A₀ : Nat → Reach` runs through
the *same* `WP.loopNatCert` certificate as `while`; `inv_init`
discharges the entry weaken and the exit weaken re-packages the
witnesses.  There is no new trusted loop rule.

Decided *against* changing `while` in place: the snapshot-free form
covers most loops with lighter VC statements, every existing user
(TreeDemo, TreeInsert, BalValueReverse, the SSZ ports) keeps compiling,
and the parallel-session fence on `Codegen/Programs/*` stays intact.
The duplicated soundness case is the price; a later migration can fold
`while` into `whileS` with a `fun _ _ _ => inv` adaptor if the
duplication starts to itch.

**3. Scale.**  VC count and VC size are O(1) in the fuel, and so is
elaboration: the monomorphized `capScanFn` proof (u64 count loaded from
the input, `n ≤ cap` precondition) elaborates in the same time at
`cap = 32`, `1024`, and `100000` — tactic execution ≈ 0.22 s and kernel
type-checking ≈ 0.23 s per run (whole-file wall clock ≈ 2.3 s, dominated
by imports; Lean 4.30.0-rc1, one warm run each).  The fuel literal only
ever appears symbolically (in `WP.loopBound` step budgets and `i < fuel`
bounds that `omega` consumes); nothing `decide`s or normalizes a
fuel-sized term.  Keep it that way: never state step budgets as computed
literals, and keep `omega` (not `decide`) on index arithmetic.

Known gap, deliberately out of scope here: a `call` *inside* a loop body
has one fixed `FnHandle`, so a per-iteration ghost contract (e.g. an
interpreter dispatch loop instantiating the handler's contract at the
current opcode) has the same shape of problem that `whileS` solves for
invariants.  The dispatch-loop bead (`.49`) should either thread the
iteration-dependent facts through registers pinned by `Reach.pin`-style
relational contracts, or extend `call` analogously if that proves too
weak.

### 3.11 Snapshot-parameterized callees and the interpreter loop (`FnHandleS`, `Stmt.callRegS`)

The gap flagged at the end of §3.10 is closed by applying the `whileS`
move to callee contracts: **`FnHandleS`** (`SAsm/Handle.lean`) carries a
postcondition *parameterized by the call's entry state* — the
auxiliary-variable triple, `sound` quantified over every entry state
satisfying `pre` — and **`Stmt.callRegS`** dispatches through a register
against a finite table of such handles, recording the entry snapshot in
its strongest postcondition.  A monomorphic `FnHandle` provably cannot
verify a state-transforming callee at a looped dispatch site (it cannot
carry the gas variant across the call).  The full analysis — invariant
shape, gas-derived fuel, the 256-handler dispatch plan, frame
descend/return as window movement over `phaseDView`, and the bead
decomposition — lives in **docs/4ch8f-interp-strategy.md**; the
end-to-end pilot is `SAsm/InterpLoopDemo.lean`
(`InterpLoopDemo.interpFn_spec`).

The same handle mechanism is the sanctioned crossing for the ZisK
accelerator seam: a `CSRS` step is *not* a block leaf (`instrOk`
rejects it); instead an accelerator wrapper is verified once at machine
level (`step_csrs` + the concrete `csrsWrite`/`csrsValid` semantics)
and packaged as a hand-proven `FnHandleS` (`SAsm/AccelStep.lean`,
`arith256ModHandle`).  Strategy and pilot (an MSB modular-exponentiation
ladder computing `x ^ e mod m` through `callRegS` at the handle):
**docs/4ch8f-crypto-strategy.md**, `SAsm/PowLadderDemo.lean`.

## 4. What this buys for `run_stateless_guest`

- The existing SSZ decode/encode routines in `Stateless/SSZ/*/Program.lean`
  are already `Program` values built from the same constructors; rewriting
  them as `Fn`s is mostly re-indenting under `block`/`when`/`while` nodes,
  after which their (currently TODO) specs in `EntrySpec.lean` become
  `Fn.Spec` statements with pure VCs.
- The check-heavy shape (validate-or-bail) maps to `when`+`assert` chains
  whose VCs are exactly the format checks — the property one actually wants
  to review.
- The routine-per-module architecture (Headers, Witness, Block, …) maps to
  `FnHandle`s, so per-module verification composes into the top-level
  `run_stateless_guest_spec` by `call` nodes rather than bespoke composition
  theorems.

## 4.9 Working manual

Day-to-day recipes (defining functions, discharging each VC kind, the
port + EEST A/B procedure, pitfalls) live in **docs/sasm-howto.md** —
that document, not this one, is what to hand an agent tasked with
verifying or porting a routine.

## 5. Milestones

1. **M1 — skeleton (this PR series):** `RegFile`, `Cond`, `Stmt`, `Region`
   (`.ro`), flattener + sizes + `#eval` tests; design doc (this file).
2. **M2 — block engine:** `execBlock`/`blockVCs` for the ALU+`LI`+`.ro`-load
   subset; `execBlock_sound`.
3. **M3 — structural soundness + tactic:** `spgen`, `spgen_sound` for
   `block`/`seq`/`ite`/`when`/`assert`/`while`; `Fn.Spec`, `Fn.sound`,
   `vcgen`; worked examples (bounds-check chain; bounded copy-style loop
   reading a `.ro` region).
4. **M4 — calls:** `FnHandle`, `call` case of `spgen_sound` via
   `cpsCallWithin`; leaf-callee restriction lifted by flattener-emitted
   ra-spill prologue/epilogue.
5. **M5 — mutable regions:** `.rw` regions, stores, `SymState`
   generalization; RLP-style demo (prefix classification + field walk) and
   first `Stateless/SSZ` routine ported.

Each milestone is a reviewable PR (or short PR chain) that builds green with
`scripts/check-forbidden-tactics.sh` / `check-axioms.sh` clean.

## 6. Alternatives considered

- **Reflective tactic over goals (deep-embed the assertion language too).**
  Rejected: the existing assertion layer (`Assertion := PartialState → Prop`)
  is shallow; re-deep-embedding it would fork the ecosystem. SAsm deep-embeds
  only *programs*, which are already deep (`List Instr`).
- **VCs by tactic recursion (a `wp_rv64`-style walker over the structure).**
  Rejected per the stated requirement: tactic recursion over program
  structure is exactly what hits `maxRecursion` and gives opaque failures
  today. A `def` + one induction theorem keeps proof-time work linear and
  failure modes declarative.
- **Expression-language leaves.** Rejected (user decision): raw `List Instr`
  leaves reuse the instruction ecosystem and the codegen path unchanged.
- **Per-block `CodeReq` unions.** Rejected: single `ofProg` per function +
  monotone extension removes the disjointness tax that dominates the RLP
  proofs.
