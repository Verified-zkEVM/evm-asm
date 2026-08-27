/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEpilogueBase

  Base pointer-restore and epilogue adapters for the corrected two-MUL
  saved-bit EXP code bundle.

  **This module is now a re-export.** All three of its theorems

    exp_pointer_restore_then_epilogue_…_spec_within
    exp_pointer_restore_then_epilogue_exit_control_…_spec_within
    exp_pointer_restore_then_epilogue_stack_tail_…_spec_within

  were ALSO declared in `SavedBitBoundarySeq.lean`, with identical statements
  (one whole declaration byte-identical, the other two proved by different
  tactic scripts) under the same namespace `EvmAsm.Evm64.Exp.Compose`. Both
  modules are in `EvmAsm.Evm64.Exp`'s import closure, so pre-module Lean was
  silently tolerating the collision; the module system's import merge rejects it:

      import …SavedBitBoundaryEpilogueBase failed, environment already contains
      'EvmAsm.Evm64.Exp.Compose.exp_pointer_restore_then_epilogue_stack_tail_…'
      from …SavedBitBoundarySeq

  This was a latent defect on `main` — see MODULES.md §5d. Neither module
  imports the other, and `SavedBitBoundarySeq.lean` is the fuller of the two
  (it carries the frame definitions and six further theorems), so the proofs
  live there and this module is kept only so its importer does not change.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

public section
