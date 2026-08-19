/-
  K67 `header_validate_post_merge` — post-loop phase theorems.

  Builds on `HeaderValidatePostMergePostLoop.lean`'s clean-run inductions to
  prove the six post-loop outcomes:

  * nonce length gate (`k67NonceLenFail`): `x12 ≠ 8` branches to the status-2
    stub at `K + 612`;
  * nonce byte failure (`k67NonceByteFail`): byte `k` of the nonce content is
    nonzero, so the `k`-th pair's `BNE x7, x0` fires to `K + 612`;
  * nonce pass (`k67NoncePass`): all 8 nonce bytes are zero, fall through to
    the ommers gate at `K + 192`;
  * ommers length gate (`k67OmmersLenFail`): `x9 ≠ 32` branches to the
    status-3 stub at `K + 620`;
  * ommers byte failure (`k67OmmersByteFail`): byte `k` differs from the
    pinned `empty_ommers_hash` constant, branch to `K + 620`;
  * ommers pass (`k67OmmersPass`): all 32 bytes match, fall through to the
    status-0 stub at `K + 596`.

  and the merged `k67PostLoop` `cpsNBranchWithin` with exits
  `[(K+596, Q0), (K+620, Q3), (K+612, Q2)]`.
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergePostLoop

namespace EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.RlpWalkNextStrictFuel
open EvmAsm.Codegen.RlpListNthItemSAsm

/-! ## The post-loop pre-state -/

/-- The register/memory state at `K + 116` (loop cleanly exited): the
    `k67LoopExit`-post shape.  `next14`/`len14` are the nonce field's
    content-end cursor and content length; `omEndW`/`omLenW` are the ommers
    field's captured content-end cursor and length. -/
def k67PLPre (sp0 base omConst endPtr : Word) (bytes : List (BitVec 8))
    (next14 len14 omEndW omLenW v6 v7 v28 v29 v30 v31 v21 : Word)
    (svals : Reg → Word) : Assertion :=
  (.x1 ↦ᵣ (K + 68)) ** (.x5 ↦ᵣ (15 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x10 ↦ᵣ next14) ** (.x11 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ len14) **
  (.x8 ↦ᵣ omEndW) ** (.x9 ↦ᵣ omLenW) **
  (.x18 ↦ᵣ next14) ** (.x19 ↦ᵣ endPtr) ** (.x20 ↦ᵣ (15 : Word)) **
  (.x21 ↦ᵣ v21) **
  (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) ** (.x30 ↦ᵣ v30) ** (.x31 ↦ᵣ v31) **
  regOwn .x13 ** regOwn .x14 ** (.x0 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ (sp0 + signExtend12 (-48 : BitVec 12))) **
  frameSlotsSaved k67Frame (sp0 + signExtend12 (-48 : BitVec 12)) svals **
  bytesRegion base bytes ** bytesRegion omConst k67OmBytes

end EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec
