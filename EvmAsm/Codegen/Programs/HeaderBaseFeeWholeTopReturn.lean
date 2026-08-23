/-
  EvmAsm.Codegen.Programs.HeaderBaseFeeWholeTopReturn

  Public names for the K73 branch seams used by the route composition and
  routine registry.  The underlying theorem bodies live in HeaderBaseFeeWholeTop;
  this small module keeps the return-name compatibility layer out of that file.
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeWholeTop

namespace EvmAsm.Codegen.HeaderBaseFeeSpec

set_option linter.defProp false in
def k73_increase_first_div_source_branch_for_return :=
  k73_increase_first_div_source_branch

set_option linter.defProp false in
def k73_increase_second_add_branch_for_return :=
  k73_increase_second_add_branch

set_option linter.defProp false in
def k73_increase_second_div_source_branch_for_return :=
  k73_increase_second_div_source_branch

set_option linter.defProp false in
def k73_increase_status_div_zero_spec_within_for_return :=
  k73_increase_status_div_zero_spec_within

end EvmAsm.Codegen.HeaderBaseFeeSpec
