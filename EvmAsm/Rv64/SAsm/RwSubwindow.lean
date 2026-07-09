/-
  EvmAsm.Rv64.SAsm.RwSubwindow

  **The multi-RW-subwindow callee adapter** (bead evm-asm-4ch8f.38.5) —
  the WRITABLE analog of `callAt`'s read-only focusing.

  Crypto callers (`bnf_mul_mod_p`, `p256_op_with`, `point_double`'s
  converter half) call a SEQUENCE of callees that each write a different
  subwindow of one global scratch arena: converters fill `…_le_a`/`_le_b`,
  the `arithMod` accelerator writes `…_le_d`, a final converter reads `_d`
  and writes the external output.  The structured layer couples a callee's
  `rw` to the enclosing window, so distinct-subwindow writes across a call
  sequence were inexpressible.  At `cpsTripleWithin` level the model is a
  pair of region equations plus a triple adapter:

  * `bytesRegion_window_focus` — carve subwindow `[j, j+n)` out of the
    arena atom: `arena = window ** windowRest` (the `**` split — the
    subwindow is genuinely OWNED by whoever holds it, everything else
    framed; no arbitrary-arena write is derivable);
  * `bytesRegion_window_update` — the SAME `windowRest` reassembles the
    arena around a REPLACED window: writing `win'` merges to
    `setBytes arena j win'` — so a callee that wrote only its window
    provably left every other subwindow untouched;
  * `cpsTripleWithin_rwWindow` / `_rwWindow_exists` — the call adapter:
    a triple over the focused window (the shape `callWithin_spec` /
    `Fn.retSpecFlat` callee contracts produce, with the callee's `rw`
    being just the subwindow) lifts to a triple over the whole arena.
    The `_exists` form takes callee posts that pin only a PROPERTY of the
    written bytes (e.g. a converter's `wsNat256 ws' 0 = value`).

  Sequencing falls out: each call in the chain focuses its own window of
  the CURRENT arena image (`setBytes` accumulate), the previously-written
  windows framed through by `wsNat256_setBytes_*`.  Decode lemmas
  (`window_readback`, `wsNat256_setBytes_window`, `wsNat256_setBytes_high`)
  connect the accumulated image to what the `arithMod` accelerator
  (`csrs_arith256Mod_spec_within`) and the final converter read.

  Composes with `abi_frame` (enclosing frame), `Fn.retSpecFlat` (#9988,
  converter contracts), the #10059 global-data model and the #10064 AUIPC
  bridge (`la`-materialized arena addresses).  Acceptance consumer:
  `bnf_mul_mod_p` (`Codegen/Programs/Bn254FieldMulModPSAsm.lean`).
-/

import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.HandleWiden
import EvmAsm.Rv64.SAsm.FramePort

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  The writable-arena split
-- ============================================================================

/-- Everything of the arena EXCEPT subwindow `[j, j+n)`: the before-prefix
    and the after-suffix.  The same rest frames a window read AND its
    replacement (`bytesRegion_window_update`). -/
def windowRest (B : Word) (ws : List (BitVec 8)) (j n : Nat) : Assertion :=
  bytesRegion B (ws.take j) **
  bytesRegion (B + BitVec.ofNat 64 (j + n)) (ws.drop (j + n))

theorem pcFree_windowRest (B : Word) (ws : List (BitVec 8)) (j n : Nat) :
    (windowRest B ws j n).pcFree :=
  pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)

/-- **Focus**: carve subwindow `[j, j+n)` out of the arena (both cut points
    dword-aligned, as every real arena layout is). -/
theorem bytesRegion_window_focus (B : Word) (ws : List (BitVec 8)) (j n : Nat)
    (hfit : j + n ≤ ws.length) (h8j : j % 8 = 0) (h8n : n % 8 = 0) :
    bytesRegion B ws
      = (bytesRegion (B + BitVec.ofNat 64 j) ((ws.drop j).take n) **
          windowRest B ws j n) := by
  unfold windowRest
  conv_lhs => rw [← List.take_append_drop j ws]
  rw [bytesRegion_append _ _ _ (by rw [List.length_take]; exact ⟨j / 8, by omega⟩)]
  rw [List.length_take, Nat.min_eq_left (by omega)]
  conv_lhs => rw [show ws.drop j = (ws.drop j).take n ++ (ws.drop j).drop n from
    (List.take_append_drop n (ws.drop j)).symm]
  rw [bytesRegion_append _ _ _ (by
    rw [List.length_take, List.length_drop]
    exact ⟨n / 8, by omega⟩)]
  rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega),
    List.drop_drop]
  have haddr : (B + BitVec.ofNat 64 j) + BitVec.ofNat 64 n
      = B + BitVec.ofNat 64 (j + n) := by
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [haddr]
  funext h
  exact propext ⟨fun hp => by xperm_hyp hp, fun hp => by xperm_hyp hp⟩

/-- Reading the freshly-written window back out of the spliced arena. -/
theorem window_readback (ws ns : List (BitVec 8)) (j : Nat)
    (hfit : j + ns.length ≤ ws.length) :
    ((setBytes ws j ns).drop j).take ns.length = ns := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, length_setBytes]
    omega
  intro k hk1 hk2
  rw [List.getElem_take, List.getElem_drop]
  have hset : k < ns.length := hk2
  have hg := getByteAt_setBytes ns ws j (j + k) hfit
  rw [if_pos ⟨by omega, by omega⟩] at hg
  have hgl : getByteAt (setBytes ws j ns) (j + k)
      = (setBytes ws j ns)[j + k]'(by rw [length_setBytes]; omega) := by
    unfold getByteAt
    rw [dif_pos]
  have hgr : getByteAt ns (j + k - j) = ns[k]'hset := by
    unfold getByteAt
    rw [dif_pos (by omega)]
    congr 1
    omega
  rw [hgl, hgr] at hg
  exact hg


/-- **Update**: the SAME rest reassembles the arena around a replaced
    window — a write that stayed inside `[j, j+n)` merges to `setBytes`,
    leaving every other subwindow untouched. -/
theorem bytesRegion_window_update (B : Word) (ws win' : List (BitVec 8))
    (j n : Nat) (hfit : j + n ≤ ws.length) (h8j : j % 8 = 0) (h8n : n % 8 = 0)
    (hwlen : win'.length = n) :
    bytesRegion B (setBytes ws j win')
      = (bytesRegion (B + BitVec.ofNat 64 j) win' ** windowRest B ws j n) := by
  have hlen' : (setBytes ws j win').length = ws.length := length_setBytes _ _ _
  rw [bytesRegion_window_focus B (setBytes ws j win') j n (by omega) h8j h8n]
  unfold windowRest
  rw [setBytes_take_of_ge win' ws j j (Nat.le_refl j),
    setBytes_drop_of_le win' ws j (j + n) (by omega)]
  congr 1
  exact congrArg (bytesRegion (B + BitVec.ofNat 64 j))
    (by rw [← hwlen]; exact window_readback ws win' j (by omega))

-- ============================================================================
-- §2  Decode lemmas across the splice accumulate
-- ============================================================================

/-- A dword read INSIDE the freshly-spliced window is a read of the new
    window's bytes. -/
theorem wsDword_setBytes_inside {ws ns : List (BitVec 8)} {j t : Nat}
    (h8 : t + 8 ≤ ns.length) (hfit : j + ns.length ≤ ws.length) :
    wsDword (setBytes ws j ns) (j + t) = wsDword ns t := by
  unfold wsDword
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, length_setBytes]
    omega
  intro k hk1 hk2
  simp only [List.length_take, List.length_drop, length_setBytes] at hk1
  rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
  have hg := getByteAt_setBytes ns ws j (j + t + k) hfit
  rw [if_pos ⟨by omega, by omega⟩] at hg
  have hgl : getByteAt (setBytes ws j ns) (j + t + k)
      = (setBytes ws j ns)[j + t + k]'(by rw [length_setBytes]; omega) := by
    unfold getByteAt
    rw [dif_pos]
  have hgr : getByteAt ns (j + t + k - j) = ns[t + k]'(by omega) := by
    unfold getByteAt
    rw [dif_pos (by omega)]
    congr 1
    omega
  rw [hgl, hgr] at hg
  exact hg

/-- A 256-bit read of the freshly-spliced 32-byte window decodes the new
    bytes (the converter-output shape the `arithMod` operands need). -/
theorem wsNat256_setBytes_inside {ws ns : List (BitVec 8)} {j : Nat}
    (h32 : ns.length = 32) (hfit : j + ns.length ≤ ws.length) :
    wsNat256 (setBytes ws j ns) j = wsNat256 ns 0 := by
  unfold wsNat256
  have h0 := wsDword_setBytes_inside (ws := ws) (ns := ns) (j := j) (t := 0)
    (by omega) hfit
  have h8 := wsDword_setBytes_inside (ws := ws) (ns := ns) (j := j) (t := 8)
    (by omega) hfit
  have h16 := wsDword_setBytes_inside (ws := ws) (ns := ns) (j := j) (t := 16)
    (by omega) hfit
  have h24 := wsDword_setBytes_inside (ws := ws) (ns := ns) (j := j) (t := 24)
    (by omega) hfit
  rw [show j + 0 = j from by omega] at h0
  rw [h0, h8, h16, h24]

/-- A 256-bit read entirely above a splice is unchanged. -/
theorem wsNat256_setBytes_high {bs ns : List (BitVec 8)} {j k : Nat}
    (h : j + ns.length ≤ k) :
    wsNat256 (setBytes bs j ns) k = wsNat256 bs k := by
  rw [← wsNat_four, ← wsNat_four]
  exact wsNat_setBytes_high h

-- ============================================================================
-- §3  The call adapter
-- ============================================================================

/-- Pull an existential out of the left conjunct (callee posts that pin
    only a PROPERTY of the written window). -/
theorem sepConj_exists_left {α : Sort _} {F : α → Assertion} {R : Assertion} :
    ∀ h, ((fun hp => ∃ a, F a hp) ** R) h ↔ ∃ a, (F a ** R) h := by
  intro h
  constructor
  · rintro ⟨h1, h2, hd, hu, ⟨a, hF⟩, hR⟩
    exact ⟨a, h1, h2, hd, hu, hF, hR⟩
  · rintro ⟨a, h1, h2, hd, hu, hF, hR⟩
    exact ⟨h1, h2, hd, hu, ⟨a, hF⟩, hR⟩

/-- **The multi-RW-subwindow call adapter**: a triple whose footprint is
    the FOCUSED subwindow — the shape a `callWithin_spec`/`Fn.retSpecFlat`
    callee contract produces when the callee's `rw` is the subwindow —
    lifts to a triple over the whole arena, everything outside the window
    provably untouched (`setBytes` merge).  Chain one instance per call,
    each on the current arena image, to sequence distinct-subwindow
    writes. -/
theorem cpsTripleWithin_rwWindow {nS : Nat} {e x : Word} {cr : CodeReq}
    {P Q : Assertion} (B : Word) (ws win' : List (BitVec 8)) (j n : Nat)
    (hfit : j + n ≤ ws.length) (h8j : j % 8 = 0) (h8n : n % 8 = 0)
    (hwlen : win'.length = n)
    (h : cpsTripleWithin nS e x cr
      (P ** bytesRegion (B + BitVec.ofNat 64 j) ((ws.drop j).take n))
      (Q ** bytesRegion (B + BitVec.ofNat 64 j) win')) :
    cpsTripleWithin nS e x cr
      (P ** bytesRegion B ws)
      (Q ** bytesRegion B (setBytes ws j win')) := by
  have hF := cpsTripleWithin_frameR (windowRest B ws j n)
    (pcFree_windowRest B ws j n) h
  refine cpsTripleWithin_weaken (fun h' hp => ?_) (fun h' hq => ?_) hF
  · rw [bytesRegion_window_focus B ws j n hfit h8j h8n] at hp
    xperm_hyp hp
  · rw [bytesRegion_window_update B ws win' j n hfit h8j h8n hwlen]
    xperm_hyp hq

/-- `setBytes` with the list's own content is the identity. -/
theorem setBytes_self (l : List (BitVec 8)) : setBytes l 0 l = l := by
  apply List.ext_getElem (by rw [length_setBytes])
  intro k hk1 hk2
  have hg := getByteAt_setBytes l l 0 k (by omega)
  rw [if_pos ⟨by omega, by omega⟩] at hg
  have hgl : getByteAt (setBytes l 0 l) k
      = (setBytes l 0 l)[k]'hk1 := by
    unfold getByteAt
    rw [dif_pos]
  have hgr : getByteAt l (k - 0) = l[k]'hk2 := by
    unfold getByteAt
    rw [show k - 0 = k from by omega, dif_pos hk2]
  rw [hgl, hgr] at hg
  exact hg

/-- Decoding a fresh 32-byte LE image recovers the value. -/
theorem wsNat256_leBytes32 (v : Nat) (hv : v < 2 ^ 256) :
    wsNat256 (leBytes32 v) 0 = v := by
  have h := wsNat256_setBytes_leBytes32 (bs := leBytes32 v) (j := 0) (v := v)
    hv (by rw [length_leBytes32])
  rwa [setBytes_self] at h

/-- **∃-sequencing**: a triple whose post existentially quantifies a datum
    (a callee that pins only a PROPERTY of its written window) composes
    with a family of continuations, one per witness — how a chain of
    subwindow-writing calls threads. -/
theorem cpsTripleWithin_seq_exists_same_cr {α : Sort _} {n1 n2 : Nat}
    {e m x : Word} {cr : CodeReq} {P Q : Assertion} {F : α → Assertion}
    (h1 : cpsTripleWithin n1 e m cr P (fun hp => ∃ a, F a hp))
    (h2 : ∀ a, cpsTripleWithin n2 m x cr (F a) Q) :
    cpsTripleWithin (n1 + n2) e x cr P Q := by
  intro R hR s hcr hPR hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQR⟩ := h1 R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, hh1, hh2, hd, hu, ⟨a, hF⟩, hRr⟩ := hQR
  have hcr1 := CodeReq.SatisfiedBy_preserved hstep1 hcr
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hR2⟩ := h2 a R hR s1 hcr1
    ⟨hp, hcompat, hh1, hh2, hd, hu, hF, hRr⟩ hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2, stepN_add_eq hstep1 hstep2, hpc2, hR2⟩

/-- `pcFree` distributes over an existential (∃-shaped callee posts). -/
theorem pcFree_exists {α : Sort _} {F : α → Assertion}
    (h : ∀ a, (F a).pcFree) :
    Assertion.pcFree (fun hp => ∃ a, F a hp) := by
  rintro hp ⟨a, hF⟩
  exact h a hp hF

#print axioms bytesRegion_window_focus
#print axioms bytesRegion_window_update
#print axioms cpsTripleWithin_rwWindow

end EvmAsm.Rv64.SAsm
