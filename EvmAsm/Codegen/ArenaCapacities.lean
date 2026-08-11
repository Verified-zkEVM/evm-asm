/-
  EvmAsm.Codegen.ArenaCapacities

  GH #10971 — fixed-arena capacity constants, in a **leaf module with no imports**.

  ## Why a leaf module rather than the sibling capacities' home

  The delete arena's bound was expressed **six ways across three files**, four of
  them as the bare literal `8192` and two as `accountStateCreatedCapacity`
  (`CreateCodeEffectLog`).  Naming it required a home visible to all six sites, and
  the two obvious candidates were both wrong:

  * `EvmAsm.Codegen.Programs.CreateCodeEffectLog`, where the sibling capacities live,
    already has six importers.  Adding three more raises hub reachability, which is
    what drives the long CI build — a measurable ongoing cost, not merely a cycle
    risk.  It would also invert the dependency direction: `StorageReadLog` imports
    exactly one module today and would come to import a high-level `Programs` module.
  * `EvmAsm.Rv64.Program` is visible everywhere but is semantically wrong: an arena
    capacity is not a RISC-V concept.

  A leaf importing **nothing** adds import edges that pull in nothing, so hub
  reachability barely moves and there is no cycle to risk by construction.
-/

namespace EvmAsm.Codegen

/-- Capacity of the `account_state_delete` arena, in 32-byte address-set entries.

    ## Why this is separate from `accountStateCreatedCapacity`

    The two are **equal today and are not the same quantity**.  Before GH #10971 the
    delete arena's bound was written as `accountStateCreatedCapacity` at two sites and
    as a bare `8192` at four more, so the guard on `account_state_delete_count` was
    correct only *by coincidence of two capacities being the same number*: resizing the
    created set independently would have silently made every delete-side bound wrong,
    and the four bare literals would not even appear in a search for the created
    capacity's name.

    ⚠️ `NonstorageEffectLog`'s `.set account_state_delete, account_state_pending + …`
    offset computation **must keep using `accountStateCreatedCapacity`**: that term is
    the *created* arena's storage size, which is what the delete arena sits after.  It
    is the one legitimate use of that constant on the delete side, and a sweep over
    "the delete bound" would have converted a correct line into a bug.

    ## Headroom (measured, not assumed)

    `account_state_created` and `account_state_delete` are `.set` aliases into the
    `nea_sort_a`/`nea_sort_b` radix scratch, which allocates
    `2 * nonstorageEffectLogCap * 112 = 8,618,624` bytes.  The delete arena's offset is
    `accountStateEntryBytes * accountStateEntryCapacity + accountStateCreatedCapacity * 32
    = 5,185,024`, leaving **3,430,016 bytes = 107,188 entries** of 32 bytes.  So this
    bound is conservative by a factor of roughly thirteen and is a *naming* fix rather
    than a bound correction — the guards were never too loose.

    Exceeding it is fail-closed: the insert refuses at capacity, the caller sets
    `account_state_overflow`, and both of that flag's consumers reject the block with
    `bv_fail_code = 58` (GH #10964). -/
def accountStateDeleteCapacity : Nat := 8192

/-- Capacity of the `account_state_created` arena, in 32-byte address-set entries —
    execution-specs' transaction-local `created_accounts`.

    It lived in `Programs.CreateCodeEffectLog` beside the AccountState table constants,
    which is where it belongs semantically but not where it was *reachable*: the two
    sites that actually mark an account created are `Programs.CreateFrameDescend` (the
    nested CREATE descent) and `Programs.BlockVerdictCreationStage` (the top-level
    creation, GH #10784 cut 2), and neither imports `CreateCodeEffectLog`.  The descent
    site consequently carried a **bare `8192`** — the same shape as the four bare delete
    bounds that motivated this module in GH #10971.  Moving the definition down costs
    nothing: `CreateCodeEffectLog` already imports this module, so its own uses are
    unaffected.

    ⚠️ Equal to `accountStateDeleteCapacity` and **not the same quantity** — see that
    declaration.  Note also that `NonstorageEffectLog`'s `.set account_state_delete`
    offset legitimately uses *this* constant, because the created arena is what the
    delete arena sits after. -/
def accountStateCreatedCapacity : Nat := 8192

/-- Capacity (entries) of the non-storage effect log — touched non-recipient accounts per tx.
    Set to 65536 (bmvmx.5.5.7.3, final capacity-chain slice): now that BOTH exec-vs-BAL
    comparators are linear — the FORWARD binary-searches the sorted agg (#9018) and the REVERSE
    _covers uses a matched-bitmap over the sorted agg (#9021) — there is no remaining super-linear
    consumer, so the cap can cover the full 200M-gas worst case.

    Worst-case bound: a nonzero value-CALL appends TWO raw records, the caller debit and the callee
    credit (ChildFrameHandlers .61.6.8), while its cheapest regular-gas charge is an existing warm
    account: GAS_WARM_ACCESS(100) + GAS_CALL_VALUE(10300) = 10400. Thus execution contributes
      2 * floor(200_000_000 / 10400) = 38_460
    raw records. CREATE and SELFDESTRUCT producer paths are more expensive per emitted effect.
    `block_verdict_withdrawal_nonstorage_effects` appends withdrawals to this SAME raw log, and
    withdrawals are bounded separately to 16 records, so the full stream bound is
      38_460 + 16 = 38_476.
    This uses the regular-gas budget only: EIP-7928 state gas is a separate block budget and cannot
    reduce the execution bound. The withdrawal contributor is named here because "separately
    bounded" is true of its count, but false of the storage it shares. The overflow flag remains a
    fail-closed runtime guard, rather than a verdict assumption.

    Cost: live consumers iterate over the recorded `count`, never `cap`, so a larger cap is
    pure reserved BSS. The exec_nonstorage_effect_log and shared radix-sort buffers are sized
    from this cap, so they scale automatically.

    It lived in `Programs.NonstorageEffectLog`, which `Programs.CreateCodeEffectLog` cannot
    import (the dependency runs the other way); moving it here lets both probe data sections
    size the shared scratch (GH #11987). -/
def nonstorageEffectLogCap : Nat := 38476

end EvmAsm.Codegen
