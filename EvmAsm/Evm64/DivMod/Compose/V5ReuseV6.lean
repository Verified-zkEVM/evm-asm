/-
  EvmAsm.Evm64.DivMod.Compose.V5ReuseV6

  Infrastructure for reusing the v5 unconditional stack spec inside `divCodeV6`.
  The embedded `evm_div_v5` sits at `base + v6V5Off` and is the last (index 11)
  element of `divCodeV6`'s `unionAll`. To frame the v5 spec into `divCodeV6` we
  need each preceding fast-path block disjoint from `divCode_v5 (base+v6V5Off)`,
  which follows from a support lemma: every address `divCode_v5 b` maps lies at
  `b + 4·K` for some `K < 353` (the v5 program is 353 instrs, laid out
  contiguously by the block offsets).

  Bead `evm-asm-dr466`.
-/

import EvmAsm.Evm64.DivMod.Compose.V5Code2
import EvmAsm.Evm64.DivMod.Compose.Base

namespace EvmAsm.Rv64

/-- A hit in a `unionAll` comes from some component block. -/
theorem CodeReq.unionAll_some_mem (crs : List CodeReq) (a : Word) (i : Instr)
    (h : (CodeReq.unionAll crs) a = some i) :
    ∃ j, ∃ (hj : j < crs.length), (crs.get ⟨j, hj⟩) a = some i := by
  induction crs with
  | nil => simp [CodeReq.unionAll, CodeReq.empty] at h
  | cons cr rest ih =>
    rw [CodeReq.unionAll_cons] at h
    simp only [CodeReq.union] at h
    cases hc : cr a with
    | some i' => exact ⟨0, by simp, by simp [hc]; rw [hc] at h; simpa using h⟩
    | none =>
      rw [hc] at h
      obtain ⟨j, hj, hjj⟩ := ih h
      exact ⟨j + 1, by simp; omega, by simpa using hjj⟩

-- NOTE: the `divCode_v5` support lemma (every address is `b + 4·K`, `K < 353`)
-- and the 11 fast-block disjointness obligations for the v5-arm reuse build on
-- `unionAll_some_mem` above. Per-block recipe (offsets 0/32/116/212/228/312/396/
-- 432/448/908/1008/1048/1068/1072; lengths from `Base.lean`'s `divK_*_len` +
-- `divK_divEpilogue_len` + `divK_div128_v5_len`, summing to 353) is in bead
-- `evm-asm-dr466`.

end EvmAsm.Rv64
