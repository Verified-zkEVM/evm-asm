/-
  EvmAsm.Evm64.DivMod.Spec.StackDispatcher

  Public stack-level dispatcher surface for issue #61.
-/

import EvmAsm.Evm64.DivMod.Spec.Unified

namespace EvmAsm.Evm64

/-!
The path-specific stack specs already carry the proof terms. This module mirrors
`Compose.Dispatcher`: it gives downstream users stable dispatcher-surface names
and a bounded branch registry while keeping the proof-bearing branch aliases
reachable from `EvmAsm.Evm64.DivMod.Spec`.
-/

abbrev evm_div_stack_spec_within_bzero := evm_div_bzero_stack_spec_within
abbrev evm_div_stack_spec_within_n1Full := evm_div_n1_stack_spec_within_word_uni
abbrev evm_div_stack_spec_within_n2Full := evm_div_n2_stack_spec_within_word_uni
abbrev evm_div_stack_spec_within_n3Full := evm_div_n3_stack_spec_within_word_uni
abbrev evm_div_stack_spec_within_n4Full := evm_div_n4_stack_spec_within_dispatch_uni

abbrev evm_mod_stack_spec_within_bzero := evm_mod_bzero_stack_spec_within
abbrev evm_mod_stack_spec_within_n1Full := evm_mod_n1_stack_spec_within_word_uni
abbrev evm_mod_stack_spec_within_n2Full := evm_mod_n2_stack_spec_within_word_uni
abbrev evm_mod_stack_spec_within_n3Full := evm_mod_n3_stack_spec_within_word_uni
abbrev evm_mod_stack_spec_within_n4Full := evm_mod_n4_stack_spec_within_dispatch_uni

inductive DivStackDispatchBranch where
  | bzero
  | n1Full
  | n2Full
  | n3Full
  | n4Full
  deriving DecidableEq, Repr

inductive ModStackDispatchBranch where
  | bzero
  | n1Full
  | n2Full
  | n3Full
  | n4Full
  deriving DecidableEq, Repr

def DivStackDispatchBranch.bound : DivStackDispatchBranch → Nat
  | .bzero => 13
  | .n1Full => unifiedDivBound
  | .n2Full => unifiedDivBound
  | .n3Full => unifiedDivBound
  | .n4Full => unifiedDivBound

def ModStackDispatchBranch.bound : ModStackDispatchBranch → Nat
  | .bzero => 13
  | .n1Full => unifiedDivBound
  | .n2Full => unifiedDivBound
  | .n3Full => unifiedDivBound
  | .n4Full => unifiedDivBound

/-- Bounded stack-level DIV dispatcher registry.

Each branch points at the proof-bearing alias named in the adjacent comment.
All nonzero-divisor branches are lifted to `unifiedDivBound`, so the surface has
a single documented bound for downstream case splitting. -/
def evm_div_stack_spec_within : List (DivStackDispatchBranch × Nat) :=
  [(.bzero, DivStackDispatchBranch.bound .bzero),     -- evm_div_stack_spec_within_bzero
   (.n1Full, DivStackDispatchBranch.bound .n1Full),   -- evm_div_stack_spec_within_n1Full
   (.n2Full, DivStackDispatchBranch.bound .n2Full),   -- evm_div_stack_spec_within_n2Full
   (.n3Full, DivStackDispatchBranch.bound .n3Full),   -- evm_div_stack_spec_within_n3Full
   (.n4Full, DivStackDispatchBranch.bound .n4Full)]   -- evm_div_stack_spec_within_n4Full

/-- Bounded stack-level MOD dispatcher registry. -/
def evm_mod_stack_spec_within : List (ModStackDispatchBranch × Nat) :=
  [(.bzero, ModStackDispatchBranch.bound .bzero),     -- evm_mod_stack_spec_within_bzero
   (.n1Full, ModStackDispatchBranch.bound .n1Full),   -- evm_mod_stack_spec_within_n1Full
   (.n2Full, ModStackDispatchBranch.bound .n2Full),   -- evm_mod_stack_spec_within_n2Full
   (.n3Full, ModStackDispatchBranch.bound .n3Full),   -- evm_mod_stack_spec_within_n3Full
   (.n4Full, ModStackDispatchBranch.bound .n4Full)]   -- evm_mod_stack_spec_within_n4Full

end EvmAsm.Evm64
