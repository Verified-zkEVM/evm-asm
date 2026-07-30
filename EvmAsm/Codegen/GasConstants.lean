/-
  EvmAsm.Codegen.GasConstants

  GH #10980 — gas constants that reach the emitted stream as *runtime multipliers*,
  in a **leaf module with no imports** (same rationale as `EvmAsm.Codegen.ArenaCapacities`).

  ## Why these two constants needed a home of their own

  Every other state-gas charge in the emitter has a compile-time byte count, so it
  goes through `liStateGasRuntime`, which does the multiply in Lean and emits a single
  `li` of the product.  The **code-deposit** charges cannot: the byte count is
  `len(contract_code)`, known only at run time, so the emitter has to put the
  *multiplier itself* into the instruction stream:

  ```
    li t1, 1530 ; mul t0, t0, t1      -- code_deposit_state_gas
    li t1, 6    ; mul t0, t0, t1      -- code_hash_gas
  ```

  That is the whole population, and it is exactly the population that
  `liStateGasRuntime`'s existence hides: a reader who checks that state-gas
  multipliers are named will find every *other* site parameterised and conclude the
  emitter has no bare literals.  The four that remain are the two deploy sites
  (nested CREATE in `Programs.NoopHalt`, top-level creation in
  `Programs.BlockVerdictCreationStage`) × the two dimensions (STATE and REGULAR).

  ## Why a leaf importing nothing

  `amsterdamCostPerStateByte` lived in `Programs.AmsterdamSystemTx`, which has many
  importers.  Moving it **down** into a module with no imports keeps the value
  reachable from the two deploy-site files at zero reachability cost — an import edge
  into a leaf pulls in nothing, so the CI build does not grow.  `AmsterdamSystemTx`
  now imports this module, so every existing user of the name still resolves it
  transitively and no other file needed touching.

  The obvious stronger alternative — define these as references to
  `EvmAsm.Stateless.SpecRef.StateGasCosts.COST_PER_STATE_BYTE` and a new
  `GasCosts.OPCODE_KECCAK256_PER_WORD`, the way `Codegen.MemoryBudgetGuard` ties
  `memoryPerWord` to `SpecRef.GasCosts.MEMORY_PER_WORD` — was **deliberately not
  taken**: it would put `SpecRef.Gas` in the reachable set of every importer of
  `AmsterdamSystemTx`.  The spec mirror is cited from each docstring instead, and
  since it holds the same numbers independently it already functions as the
  cross-check a shared definition would have given.
-/

namespace EvmAsm.Codegen

/-- execution-specs Amsterdam `StateGasCosts.COST_PER_STATE_BYTE` (`vm/gas.py:40`).

    The v0.4.0 conformance target (`tests-zkevm@v0.4.0`) uses a **constant** 1530.  A
    later eip-8037 draft scales it with the block gas limit; the v0.4.0 fixtures do
    **not** — `header.gas_used` there is independent of `gas_limit`.  A refactor
    (drj99.1.2) once made this a runtime `evm_state_gas_per_byte` load, which regressed
    every state-gas charge; see `liStateGasRuntime` for that history.

    Mirrored independently at `EvmAsm/Stateless/SpecRef/Gas.lean:49`, and note the spec
    marks the enclosing class *"may be patched at runtime by a future gas repricing
    utility"* (`vm/gas.py:30-31`) — which is the argument for one name rather than five
    literals. -/
def amsterdamCostPerStateByte : Nat := 1530

/-- execution-specs Amsterdam `GasCosts.OPCODE_KECCAK256_PER_WORD` (`vm/gas.py:229`).

    Reaches the emitted stream only via `code_hash_gas` at the two deploy sites
    (`vm/interpreter.py:222-226`: `OPCODE_KECCAK256_PER_WORD * ceil32(ulen(code)) // 32`),
    charged against the **REGULAR** gas pool — the sibling `code_deposit_state_gas`
    immediately below it goes to the **STATE** pool.  The two literals sit two lines
    apart at each site and are charged to different pools, which is the other reason to
    name them: a reader cannot tell them apart by position. -/
def amsterdamKeccak256PerWord : Nat := 6

/- Tripwires.  These are the point of the module: the two bare literals had no guard of
   any kind, so a repricing that edited one deploy site and missed the other would have
   produced a *silently* asymmetric emitter.  `#guard` fails the build.
   (A `/-- -/` docstring is not accepted on `#guard`, hence the plain comment.) -/
#guard amsterdamCostPerStateByte = 1530
#guard amsterdamKeccak256PerWord = 6

end EvmAsm.Codegen
