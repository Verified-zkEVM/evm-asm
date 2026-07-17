/-
  EvmAsm.Rv64.SAsm.MultiRw

  Multiple writable regions for SAsm functions (bead evm-asm-4ch8f.67).

  ## The design decision (recorded)

  A routine that writes TWO OR MORE independent writable pointers (e.g. a
  `dst` buffer via `SB` plus an output-length dword at a separate pointer
  via `SD`, with a live gap between them that the routine does not own)
  owns:

  - region 1 as the function's primary `rw : RwRegion` (contents threaded
    through the symbolic state `ws` as usual), and
  - regions 2, 3, … as `bytesRegion` conjuncts of the ambient assertion
    `A`, each written through a `Stmt.blockAt` node focused at the region's
    pointer register.

  This is the *assertion-atom-routable store* design of the bead, realized
  at block granularity by the existing `blockAt` machinery — NO engine or
  AST change.  Why this rather than `rw : List RwRegion`:

  - **Soundness is already proven.**  `Stmt.sound`'s `blockAt` case routes
    every store of the focused block into the window carved out of `A` at
    `rf.get ptr` and frames the primary `rw` bytes AND the read-only region
    across the block (`Stmt.sp`: `ws' = ws`, `A'' = bytesRegion (rf.get p)
    win' ** rest`).  A `List RwRegion` engine would need a multi-window
    re-proof of the ~700-line machine-level `execBlock_sound`.
  - **Disjointness is structural, not arithmetic.**  The regions live under
    `**` in `asrtM`: overlapping regions make the precondition
    *unsatisfiable* (no machine state satisfies it), so a misrouted store
    can never be exploited — strictly stronger than a pairwise-disjointness
    side condition on an arithmetic routing test.  The only arithmetic
    hypotheses are the per-access routing facts the VCs already demand
    (an access must fit inside the region that owns its address).
  - **Block granularity loses nothing.**  `seq` of `block`/`blockAt` leaves
    flattens to the same contiguous instruction stream with zero
    synthesized instructions, so ANY interleaving of stores to different
    regions is expressible by cutting the instruction list at
    region-switch boundaries; values cross the cut in registers, exactly
    as the machine code does anyway.
  - **Backward compatible by construction.**  Nothing in `Fn`, `Stmt`,
    `Reach`, or the engine changes; every existing single-`rw` function
    compiles and verifies unchanged.

  The demo `twoRwFn` below is a genuine two-writable-region function
  (two independent free pointers `dst` and `cnt`): it copies 8 bytes from
  the read-only region into region A (`dst`, the primary `rw`) and writes
  the copied byte count into region B (`cnt`, an ambient `bytesRegion`
  atom).  Its post pins BOTH regions as functions of the input:
  `ws = bs` and `A = ⌜…⌝ ** bytesRegion cnt (dwordBytes 8)`.

  Consumers: `swd_minimal_copy` (bead .12.9) and every "result buffer +
  length/count dword" routine.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic

namespace EvmAsm.Rv64

/-- Unpacking a packed 8-byte list gives the list back (the inverse
    direction of `packBytes_dwordBytes`). -/
theorem dwordBytes_packBytes (bs : List (BitVec 8)) (h : bs.length = 8) :
    dwordBytes (packBytes bs) = bs := by
  apply List.ext_getElem (by simp [h])
  intro i hi hbs
  simp only [length_dwordBytes] at hi
  interval_cases i <;>
    simp [dwordBytes, extractByte_packBytes _ _ (by omega) (by omega)]

namespace SAsm

/-- Discharge the meat of a second-writable-region `.focus` VC: with the
    pointer register pinned to the region base and the ambient assertion
    holding the region's wf fact and bytes, produce the window/rest pair
    and the window well-formedness that `blockAt` demands. -/
theorem focus_rwAtom {p : Reg} {b : Word} {n : Nat} {w : List (BitVec 8)}
    {rf : RegFile} (hptr : rf.get p = b) (hlen : w.length = n) :
    ∀ hp, (⌜RwRegion.wf ⟨b, n⟩⌝ ** bytesRegion b w) hp →
      (bytesRegion (rf.get p) w ** ⌜RwRegion.wf ⟨b, n⟩⌝) hp
        ∧ RwRegion.wf ⟨rf.get p, w.length⟩ := by
  intro hp hhp
  have hwf := ((sepConj_pure_left hp).mp hhp).1
  constructor
  · rw [hptr]
    xperm_hyp hhp
  · rw [hptr, hlen]
    exact hwf

namespace MultiRw

/-- Region-A block: copy the read-only region's first dword into the
    primary writable region (`a2` = src pointer, `a0` = dst pointer). -/
def copyBlock : List Instr := [.LD .x5 .x12 0, .SD .x10 .x5 0]

/-- Region-B block: write the copied byte count (8) into the count dword
    (`a1` = cnt pointer). -/
def countBlock : List Instr := [.LI .x6 8, .SD .x11 .x6 0]

/-- Focus relation of the count store: the window is region B's bytes at
    the (pinned) pointer in `a1`; the remainder is region B's wf fact. -/
def countWinR (cnt : Word) (w2 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion →
      List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ win rest =>
    rf.get .x11 = cnt ∧ win = w2 ∧ rest = ⌜RwRegion.wf ⟨cnt, 8⟩⌝

open Stmt in
/-- Copy into region A (primary `rw`), then write the count into region B
    (ambient atom, via `blockAt`). -/
def twoRwBody (cnt : Word) (w2 : List (BitVec 8)) : Stmt :=
  .block "copyA" copyBlock ;;;
  .blockAt "countB" .x11 (countWinR cnt w2) countBlock

/-- **The two-writable-region demo function.**  `src`, `dst`, and `cnt` are
    three independent pointers: `⟨src, bs⟩` is the read-only region, region
    A is the primary `rw` at `dst` (8 bytes), and region B is the count
    dword at `cnt`, owned as a `bytesRegion` atom of the ambient assertion.
    The post pins region A to the copied input bytes and region B to the
    count — both functions of the input, no existentials. -/
def twoRwFn (src dst cnt : Word) (bs w2 : List (BitVec 8)) : Fn where
  name := "twoRw"
  region := ⟨src, bs⟩
  rw := ⟨dst, 8⟩
  pre := fun rf _ A =>
    rf.get .x10 = dst ∧ rf.get .x11 = cnt ∧ rf.get .x12 = src ∧
    A = (⌜RwRegion.wf ⟨cnt, 8⟩⌝ ** bytesRegion cnt w2)
  post := fun rf ws A =>
    rf.get .x10 = dst ∧ rf.get .x11 = cnt ∧ rf.get .x12 = src ∧
    ws = bs ∧
    A = (⌜RwRegion.wf ⟨cnt, 8⟩⌝ ** bytesRegion cnt (dwordBytes 8))
  body := twoRwBody cnt w2

-- The emitted code is the two blocks back to back: block-granular store
-- routing adds zero instructions.
#guard ((twoRwBody 0 []).flatten 0 : List Instr) = copyBlock ++ countBlock

-- Position independence: no PC-relative instructions.
#guard ((twoRwBody 0 []).flatten 0 = (twoRwBody 0 []).flatten 0x80000000)

/-- An `LD` that misses the writable window reads the read-only region;
    stated fully resolved (address and value) for one-`rw` chaining. -/
private theorem execInstrRF_ld_romiss (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (v : Word)
    (hmiss : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8)
    (hv : ro.dwordAt (rf.get rs1 + signExtend12 ofs) = v) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs) = (rf.set rd v, ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg hmiss, hv]

section Demo

variable (src dst cnt : Word) (bs w2 : List (BitVec 8))

/-- The copy block's engine run, fully resolved: `t0 := packBytes bs`,
    region A := the input bytes. -/
private theorem copy_engine (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = dst) (hx12 : rf.get .x12 = src)
    (hws : ws.length = 8) (hbs : bs.length = 8) (hne : src ≠ dst) :
    execBlock ⟨src, bs⟩ dst rf ws copyBlock
      = (rf.set .x5 (packBytes bs), bs) := by
  have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : rf.get .x12 + signExtend12 (0 : BitVec 12) = src := by
    rw [hx12, hs0]; bv_omega
  rw [show copyBlock = [.LD .x5 .x12 0, .SD .x10 .x5 0] from rfl]
  rw [execBlock_cons, execInstrRF_ld_romiss _ _ _ _ _ _ _ (packBytes bs)
    (by
      unfold inRw
      rw [haddr]
      intro hin
      exact hne (by bv_omega))
    (by
      unfold Region.dwordAt
      rw [haddr]
      show packBytes ((bs.drop (src - src).toNat).take 8) = _
      rw [show ((src - src : Word)).toNat = 0 from by bv_omega,
        List.drop_zero, List.take_of_length_le (by omega)])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0
    (by
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10, hs0]
      bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), execBlock_nil,
    setBytes_dword_full _ _ hws, dwordBytes_packBytes _ hbs]

/-- The count block's engine run, fully resolved: `t1 := 8`, region B :=
    the count dword. -/
private theorem count_engine (reg : Region) (rf : RegFile)
    (hx11 : rf.get .x11 = cnt) (hw2 : w2.length = 8) :
    execBlock reg cnt rf w2 countBlock = (rf.set .x6 8, dwordBytes 8) := by
  have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  rw [show countBlock = [.LI .x6 8, .SD .x11 .x6 0] from rfl]
  rw [execBlock_cons,
    show execInstrRF reg cnt rf w2 (.LI .x6 8) = (rf.set .x6 8, w2) from rfl]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0
    (by
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), hx11, hs0]
      bv_omega)]
  rw [RegFile.get_set_self _ _ _ (by decide), execBlock_nil,
    setBytes_dword_full _ _ hw2]

/-- Address side conditions of the copy block: the load routes to the
    read-only region (it misses region A), the store routes into region A
    at offset 0, aligned. -/
private theorem copy_blockVCs (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = dst) (hx12 : rf.get .x12 = src)
    (hws : ws.length = 8) (hbs : bs.length = 8) (hne : src ≠ dst) :
    blockVCs ⟨src, bs⟩ dst rf ws copyBlock := by
  have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have haddr : rf.get .x12 + signExtend12 (0 : BitVec 12) = src := by
    rw [hx12, hs0]; bv_omega
  have hmiss : ¬ inRw dst ws (rf.get .x12 + signExtend12 (0 : BitVec 12)) 8 := by
    unfold inRw
    rw [haddr]
    intro hin
    exact hne (by bv_omega)
  rw [show copyBlock = [.LD .x5 .x12 0, .SD .x10 .x5 0] from rfl]
  refine ⟨?_, ?_, trivial⟩
  · show (if inRw dst ws (rf.get .x12 + signExtend12 0) 8
      then _ else Region.loadOk _ _ _)
    rw [if_neg hmiss]
    refine ⟨?_, ?_⟩
    · rw [haddr]
      show 8 ∣ ((src - src : Word)).toNat
      rw [show ((src - src : Word)).toNat = 0 from by bv_omega]
      exact ⟨0, rfl⟩
    · rw [haddr]
      show ((src - src : Word)).toNat + 8 ≤ bs.length
      rw [show ((src - src : Word)).toNat = 0 from by bv_omega]
      omega
  · -- the store VC, after stepping the load
    rw [execInstrRF_ld_romiss (⟨src, bs⟩ : Region) dst rf ws .x5 .x12 0
      (Region.dwordAt ⟨src, bs⟩ (rf.get .x12 + signExtend12 0)) hmiss rfl]
    dsimp only
    have haddr2 : ∀ v : Word,
        (rf.set .x5 v).get .x10 + signExtend12 (0 : BitVec 12) = dst := by
      intro v
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10, hs0]
      bv_omega
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [haddr2, show ((dst - dst : Word)).toNat = 0 from by bv_omega]
      show 0 + 8 ≤ ws.length
      omega
    · rw [haddr2, show ((dst - dst : Word)).toNat = 0 from by bv_omega]
      exact ⟨0, rfl⟩

/-- Address side conditions of the count block: the store fits region B's
    window at offset 0, aligned. -/
private theorem count_blockVCs (reg : Region) (rf : RegFile)
    (hx11 : rf.get .x11 = cnt) (hw2 : w2.length = 8) :
    blockVCs reg cnt rf w2 countBlock := by
  have haddr : (((rf.set .x6 8).get .x11 + signExtend12 (0 : BitVec 12))
      - cnt).toNat = 0 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6), hx11,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  simp only [countBlock, blockVCs, loadSem, storeSem, aluSem, execInstrRF,
    inRw, haddr]
  exact ⟨trivial, ⟨by omega, ⟨0, rfl⟩⟩, trivial⟩

/-- **The two-writable-region triple.**  Hypotheses: both declared regions
    are well-formed (region B's wf fact travels inside the ambient
    assertion) and the load's routing disjointness `src ≠ dst` (regions
    that actually overlap make the precondition unsatisfiable via `**`,
    so no store can ever be misrouted; `src ≠ dst` is only what resolves
    the load's routing `if` in the proof). -/
theorem twoRwFn_spec (base : Word)
    (hro : Region.wf ⟨src, bs⟩) (hrwA : RwRegion.wf ⟨dst, 8⟩)
    (hbs : bs.length = 8) (hw2 : w2.length = 8) (hne : src ≠ dst) :
    (twoRwFn src dst cnt bs w2).Spec base := by
  vcgen
  case region => exact ⟨hro, hrwA⟩
  case twoRw.copyA.mem =>
    rintro rf ws A hws ⟨hx10, hx12, hx11, hA⟩
    exact copy_blockVCs src dst bs rf ws hx10 hx11 hws hbs hne
  case twoRw.countB.focus =>
    rintro rf ws A ⟨rf₀, ws₀, hlen₀, ⟨hx10, hx11, hx12, hA⟩, hrf, -⟩ hApc hp hhp
    dsimp only [twoRwFn] at hlen₀ hrf
    rw [copy_engine src dst bs rf₀ ws₀ hx10 hx12 hlen₀ hbs hne] at hrf
    have hx11' : rf.get .x11 = cnt := by
      rw [hrf, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      exact hx11
    obtain ⟨hpair, hwf⟩ := focus_rwAtom hx11' hw2 hp (hA ▸ hhp)
    exact ⟨w2, ⌜RwRegion.wf ⟨cnt, 8⟩⌝, ⟨hx11', rfl, rfl⟩, hpair,
      pcFree_pure, hwf⟩
  case twoRw.countB.mem =>
    rintro rf ws A win rest hws hreach ⟨hx11', hwin, hrest⟩ hsat
    rw [hx11', hwin]
    exact count_blockVCs cnt w2 _ rf hx11' hw2
  case twoRw.post =>
    rintro rf' ws' A''
      ⟨rf, A, win, rest, hlen, hreach, hsat, ⟨hx11', hwin, hrest⟩, hrf', hA''⟩
    obtain ⟨rf₀, ws₀, hlen₀, ⟨hx10, hx11, hx12, hA⟩, hrf, hws⟩ := hreach
    dsimp only [twoRwFn] at hlen₀ hrf hws hrf' hA'' ⊢
    rw [copy_engine src dst bs rf₀ ws₀ hx10 hx12 hlen₀ hbs hne] at hrf hws
    rw [hx11', hwin, count_engine cnt w2 _ rf hx11' hw2] at hrf' hA''
    rw [hrest] at hA''
    subst hrf'
    refine ⟨?_, ?_, ?_, hws, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6), hrf,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5)]
      exact hx10
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6)]
      exact hx11'
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6), hrf,
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]
      exact hx12
    · rw [hA'', sepConj_comm']

end Demo


end MultiRw

end SAsm
end EvmAsm.Rv64
