/-
  EvmAsm.Rv64.RLP.WalkCall

  Caller-side composition for the cursor-walk RLP decoders. The `tx_*_decode` /
  header decoders added in #9503/#9504 are **non-leaf**: they open a stack frame
  and make nested `jal ra, <primitive>` calls into the verified leaf primitives
  (`rlp_walk_init`, `rlp_walk_next`, `rlp_content_to_u64`, `rlp_content_to_u256_be`).

  This file provides the foundational piece the leaf CPS framework was missing:
  `cpsCallWithin`, which threads a callee's `cpsTripleWithin` (entry → `ra &&& ~~~1`)
  through a `jal ra, callee` call site. A `jal ra` at `base` sets `ra := base + 4`
  and jumps to the callee; the callee returns to `(base + 4) &&& ~~~1 = base + 4`
  (the caller's next instruction, which is 4-aligned), so the whole call is a single
  composite step `base → base + 4` carrying the callee's effect.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics

/--
**Call composition.** Given a `jal .x1 off` (i.e. `jal ra, callee`) at `base` whose
target is `callee_entry = base + signExtend21 off`, and a callee whose spec runs
`callee_entry → (base + 4) &&& ~~~1` with `ra` set to the return address
`base + 4`, the call as a whole is a `base → (base + 4) &&& ~~~1` step that
preserves the callee's frame `P` and yields its postcondition `Q`. The caller's
incoming `ra` (`raOld`) is overwritten.
-/
theorem cpsCallWithin {n : Nat} {base callee_entry : Word} {off : BitVec 21} {cr : CodeReq}
    {P Q : Assertion} {raOld : Word} (hP : P.pcFree)
    (hjal : ∀ a i, CodeReq.singleton base (.JAL .x1 off) a = some i → cr a = some i)
    (hentry : base + signExtend21 off = callee_entry)
    (hcallee : cpsTripleWithin n callee_entry ((base + 4) &&& ~~~1) cr
      ((.x1 ↦ᵣ (base + 4)) ** P) Q) :
    cpsTripleWithin (1 + n) base ((base + 4) &&& ~~~1) cr ((.x1 ↦ᵣ raOld) ** P) Q := by
  have hjal_spec := cpsTripleWithin_extend_code hjal
    (cpsTripleWithin_frameR P hP (jal_spec_within .x1 raOld off base (by nofun)))
  rw [hentry] at hjal_spec
  exact cpsTripleWithin_seq_perm_same_cr (fun h hp => hp) hjal_spec hcallee

end EvmAsm.Rv64.RLP
