/-
  EvmAsm.Codegen.Programs.CellStoreIdioms

  **Two composition idioms for `.data`-cell initialisation blocks**, both
  generic in the routine's `CodeReq` (GH #13246).

  Both witness-ingest DB builders — `witness_codes_index_build` and
  `witness_index_build` — open with a run of `auipc`/`addi`/`sd` triples that
  clear or publish one `.data` cell each: thirteen of them before the
  empty-section branch, four more in the publish tail.  Composed naively that
  is seventeen permutation searches over a growing twenty-five atom heap.

  * `chainK` sequences two segments that share a carried context `K` by pure
    reassociation of `**`, so the cost of a chain is linear in its length and
    no permutation search happens at the joins at all.
  * `laStoreOwn` / `laStoreAt` are the store idiom itself, at an owned cell and
    at a cell whose prior value is known.  With `rs = x0` (and `x0 ↦ᵣ 0` in the
    ambient) `laStoreOwn` is the zeroing form.

  Code membership is hypothesis-shaped throughout, so each call site discharges
  it by evaluation against its own routine's `CodeReq` (`code_mem`).
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.CellStoreIdioms

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

set_option maxRecDepth 8000


/-- **Chaining two segments that share a carried context `K`.**  `K` is the
    part of the ambient both segments read or overwrite; `P₁/Q₁` and `P₂/Q₂`
    are the disjoint resources each segment owns.  Pure reassociation — no
    permutation search, so the cost does not grow with the chain length. -/
theorem chainK {cr : CodeReq} {n1 n2 : Nat} {A E F : Word}
    {K P1 Q1 P2 Q2 : Assertion}
    (hQ1 : Q1.pcFree) (hP2 : P2.pcFree)
    (h1 : cpsTripleWithin n1 A E cr (K ** P1) (K ** Q1))
    (h2 : cpsTripleWithin n2 E F cr (K ** P2) (K ** Q2)) :
    cpsTripleWithin (n1 + n2) A F cr (K ** P1 ** P2) (K ** Q1 ** Q2) := by
  have h1f := cpsTripleWithin_frameR P2 hP2 h1
  have h2f := cpsTripleWithin_frameR Q1 hQ1 h2
  have hmid : ∀ h, ((K ** Q1) ** P2) h → ((K ** P2) ** Q1) h := by
    intro h hp
    rw [sepConj_assoc', sepConj_comm' Q1 P2, ← sepConj_assoc'] at hp
    exact hp
  have hseq := cpsTripleWithin_seq_perm_same_cr hmid h1f h2f
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hseq
  · rw [← sepConj_assoc'] at hp; exact hp
  · rw [sepConj_assoc', sepConj_comm' Q2 Q1] at hq; exact hq

/-- **The `la`/`sd` store idiom**: `auipc t0,hi ; addi t0,t0,lo ; sd rs,0(t0)`
    writes `rs` into the `.data` cell `C`.  With `rs = x0` (and `x0 ↦ᵣ 0` in
    the ambient) this is the zeroing form; with any other `rs` it publishes
    that register's value.  Code membership is hypothesis-shaped so each call
    site discharges it by evaluation against its own routine's `CodeReq`. -/
theorem laStoreOwn {cr : CodeReq} (rs : Reg) (A C v : Word)
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      cr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      cr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 rs (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 A (A + 12) cr
      (((rs ↦ᵣ v) ** memOwn C) ** regOwn .x5)
      (((.x5 : Reg) ↦ᵣ C) ** (rs ↦ᵣ v) ** (C ↦ₘ v)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun vOld => ?_)
  have hla := la_materialize_within .x5 vOld A C (by decide) hrange hau had
  have hstore := liftCode (cr' := cr)
    (sd_spec_gen_own_within .x5 rs C v (0 : BitVec 12) (A + 8)) hsd
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show C + (0 : Word) = C from by bv_omega,
    show (A + 8 : Word) + 4 = A + 12 from by bv_omega] at hstore
  have hf := cpsTripleWithin_frameR ((rs ↦ᵣ v) ** memOwn C) (by pcf) hla
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hf hstore))


/-- **The `la`/`sd` store idiom at a KNOWN old cell value.**  Same three
    instructions as `laStoreOwn`; the pre pins the cell's prior contents
    instead of merely owning them, which is what a second write to a cell the
    same routine already initialised needs. -/
theorem laStoreAt {cr : CodeReq} (rs : Reg) (A C vOld v : Word)
    (hrange : laInRange A C)
    (hau : ∀ a i, CodeReq.singleton A (.AUIPC .x5 (Rv64.laHi A C)) a = some i →
      cr a = some i)
    (had : ∀ a i, CodeReq.singleton (A + 4) (.ADDI .x5 .x5 (Rv64.laLo A C)) a = some i →
      cr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (A + 8) (.SD .x5 rs (0 : BitVec 12)) a = some i →
      cr a = some i) :
    cpsTripleWithin 3 A (A + 12) cr
      (((rs ↦ᵣ v) ** (C ↦ₘ vOld)) ** regOwn .x5)
      (((.x5 : Reg) ↦ᵣ C) ** (rs ↦ᵣ v) ** (C ↦ₘ v)) := by
  refine cpsTripleWithin_of_forall_regIs_to_regOwn (fun vR => ?_)
  have hla := la_materialize_within .x5 vR A C (by decide) hrange hau had
  have hstore := liftCode (cr' := cr)
    (sd_spec_gen_within .x5 rs C v vOld (0 : BitVec 12) (A + 8)) hsd
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show C + (0 : Word) = C from by bv_omega,
    show (A + 8 : Word) + 4 = A + 12 from by bv_omega] at hstore
  have hf := cpsTripleWithin_frameR ((rs ↦ᵣ v) ** (C ↦ₘ vOld)) (by pcf) hla
  exact cpsTripleWithin_mono_nSteps (show 2 + 1 ≤ 3 by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq)
      (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hf hstore))


/-- **The two argument moves** `mv s0, a0 ; mv s1, a1` that both witness-ingest
    builders use to park their arguments in callee-saved registers (idx 15…16).
    Asymmetric by construction: `a0→s0` and `a1→s1` are different pairs, so a
    swap would not typecheck against the post.

    `EvmAsm.Codegen.WitnessCodesLookupSpec.wcbMv2Simple` is the `wcbCr`-pinned
    predecessor of this lemma; repointing it here is a mechanical follow-up
    deliberately not folded into the proof PR that introduced this module. -/
theorem mvArgPair {cr : CodeReq} (A ptr len oldPtr oldLen : Word)
    (h1 : ∀ a i, CodeReq.singleton A (.MV .x8 .x10) a = some i → cr a = some i)
    (h2 : ∀ a i, CodeReq.singleton (A + 4) (.MV .x9 .x11) a = some i →
      cr a = some i) :
    cpsTripleWithin 2 A (A + 8) cr
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x8 : Reg) ↦ᵣ oldPtr) ** ((.x9 : Reg) ↦ᵣ oldLen))
      (((.x10 : Reg) ↦ᵣ ptr) ** ((.x11 : Reg) ↦ᵣ len) **
        ((.x8 : Reg) ↦ᵣ ptr) ** ((.x9 : Reg) ↦ᵣ len)) := by
  have hmv1 := liftCode (cr' := cr)
    (mv_spec_gen_within .x8 .x10 ptr oldPtr A (by decide)) h1
  have hmv2 := liftCode (cr' := cr)
    (mv_spec_gen_within .x9 .x11 len oldLen (A + 4) (by decide)) h2
  rw [show (A + 4 : Word) + 4 = A + 8 from by bv_omega] at hmv2
  have hf := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ len) ** ((.x9 : Reg) ↦ᵣ oldLen)) (by pcf) hmv1
  have hf2 := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ ptr) ** ((.x8 : Reg) ↦ᵣ ptr)) (by pcf) hmv2
  have hseq := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simp only [sepConj_assoc'] at hp ⊢
    xperm_chunked hp) hf hf2
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_chunked hp)
    (fun _ hq => by xperm_chunked hq) hseq

end EvmAsm.Codegen.CellStoreIdioms
