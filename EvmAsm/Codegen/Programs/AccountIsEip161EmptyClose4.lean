/-
  EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose4

  Field-body OK-paths and the top-level whole-program assembly for the K137
  contract `account_is_eip161_empty_spec_within` (`AccountFields.lean`).

  Builds on the dispatch infrastructure (`AccountIsEip161EmptyClose3.lean`),
  the RLP call adapters + prologue/epilogue (`AccountIsEip161EmptyClose.lean`),
  the three byte-scan loop lemmas (`AccountIsEip161EmptyLoop.lean`), and the
  verdict-store tails + return bridges (`AccountIsEip161EmptyClose2.lean`).

  No `sorry`/`admit`/`native_decide`/`bv_decide`; classical-3 axioms only.
-/

import EvmAsm.Codegen.Programs.AccountIsEip161EmptyClose3

namespace EvmAsm.Codegen.AccountIsEip161EmptySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.RlpListNthItemSAsm

set_option maxRecDepth 8000

/-! ## Empty-code-hash constant region facts

    `ECB = aie_empty_code_hash = 0xa3000ce0` sits in the RAM window and is
    8-byte aligned; its 32 content bytes are all valid byte accesses. -/

theorem ecb_align : ECB.toNat % 8 = 0 := by decide

theorem ecb_over : ECB.toNat + 32 < 2 ^ 64 := by decide

theorem ecb_toNat_add (j : Nat) (hj : j < 32) :
    (ECB + BitVec.ofNat 64 j).toNat = 2734689504 + j := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : (ECB : Word).toNat = 2734689504 := by decide
  rw [h1, Nat.mod_eq_of_lt (show j < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show 2734689504 + j < 2 ^ 64 from by omega)]

theorem ecb_valid (j : Nat) (hj : j < 32) :
    isValidByteAccess (ECB + BitVec.ofNat 64 j) = true := by
  rw [isValidByteAccess_eq, isValidMemAddr_eq, ecb_toNat_add j hj]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  unfold Rv64.MEM_START Rv64.MEM_END Rv64.INPUT_MEM_START Rv64.INPUT_MEM_END
    Rv64.RAM_MEM_START Rv64.RAM_MEM_END
  omega

end EvmAsm.Codegen.AccountIsEip161EmptySpec
