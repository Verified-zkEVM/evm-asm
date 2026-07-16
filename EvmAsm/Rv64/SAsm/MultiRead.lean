/-
  EvmAsm.Rv64.SAsm.MultiRead

  Multiple read-only inputs for SAsm functions: the read-side mirror of
  `MultiRw`/`blockAt`, realized by the new `Stmt.readAt` focus node.

  ## The design decision (recorded)

  A routine that reads from TWO OR MORE independent read-only pointers
  (e.g. a field-arithmetic precompile whose two operands `a0`, `a1` are
  arbitrary 32-byte buffers — never guaranteed contiguous) cannot express
  those inputs as the function's single `region : Region`.  Instead it owns:

  - region 1, …, k as `bytesRegion` conjuncts of the ambient assertion `A`,
    each read through a `Stmt.readAt` node focused at the region's pointer
    register, and
  - the function's writable window as the primary `rw : RwRegion` (contents
    threaded through the symbolic state `ws` as usual).

  This is the exact mirror of `MultiRw`'s *store* design: `blockAt` swaps the
  writable window for an ambient region while the read-only `region` stays
  fixed; `readAt` swaps the read-only source for an ambient region while the
  writable `rw` stays fixed.  Because a read-only region's bytes are
  immutable, the ambient assertion is threaded UNCHANGED across a `readAt`
  block (simpler than `blockAt`, which must write the window back).  The
  same soundness argument applies: inside the block, a load that misses the
  writable window reads the focused ambient region's bytes and nothing else
  (`Stmt.sound`'s `readAt` case), disjointness is structural via `**` (an
  overlapping region makes the precondition unsatisfiable), and block
  granularity loses nothing (values cross a region-switch cut in registers).

  The demo `multiReadFn` below is the template for `bnfMulModP` /
  `secfMulModP`: it reads a dword from EACH of two independent read-only
  buffers `a0`, `a1` (both ambient `bytesRegion` atoms, allowed to coincide
  — a squaring `a0 = a1` — or to differ), sums them, and writes the result
  through the writable window `dst`.  Its post pins the window to the
  function of the two inputs and both read buffers to their (unchanged)
  input bytes.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64

namespace SAsm

namespace MultiRead

/-- Focus relation of the first read: the region bytes are `bs0` at the
    pointer pinned in `a0` (`x10`); the remainder is the second buffer. -/
def roA0 (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rst => rf.get .x10 = a0 ∧ rob = bs0 ∧ rst = bytesRegion a1 bs1

/-- Focus relation of the second read: the region bytes are `bs1` at the
    pointer pinned in `a1` (`x11`); the remainder is the first buffer. -/
def roA1 (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) :
    RegFile → List (BitVec 8) → Assertion → List (BitVec 8) → Assertion → Prop :=
  fun rf _ _ rob rst => rf.get .x11 = a1 ∧ rob = bs1 ∧ rst = bytesRegion a0 bs0

open Stmt in
/-- Read a dword from `a0` (focused), then from `a1` (focused), then sum and
    write the result to the writable window `dst` (primary `rw`). -/
def multiReadBody (a0 a1 : Word) (bs0 bs1 : List (BitVec 8)) : Stmt :=
  .readAt "readA0" .x10 (roA0 a0 a1 bs0 bs1) [.LD .x5 .x10 0] ;;;
  .readAt "readA1" .x11 (roA1 a0 a1 bs0 bs1) [.LD .x6 .x11 0] ;;;
  .block "write" [.ADD .x7 .x5 .x6, .SD .x12 .x7 0]

/-- **The two-read-only-region demo function.**  `a0`, `a1`, `dst` are three
    independent pointers: `a0`, `a1` are read-only 8-byte buffers held as
    ambient `bytesRegion` atoms, `dst` is the writable window (primary `rw`).
    The post pins `dst` to the dword sum of the two inputs and both read
    buffers to their input bytes — all functions of the input, no
    existentials. -/
def multiReadFn (a0 a1 dst : Word) (bs0 bs1 : List (BitVec 8)) : Fn where
  name := "multiRead"
  region := Region.empty
  rw := ⟨dst, 8⟩
  pre := fun rf _ A =>
    rf.get .x10 = a0 ∧ rf.get .x11 = a1 ∧ rf.get .x12 = dst ∧
    A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
  post := fun rf ws A =>
    rf.get .x12 = dst ∧
    ws = dwordBytes (packBytes bs0 + packBytes bs1) ∧
    A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
  body := multiReadBody a0 a1 bs0 bs1

-- The emitted code is the two focus blocks and the write block back to
-- back: read-side focus routing adds zero instructions.
#guard ((multiReadBody 0 0 [] []).flatten 0 : List Instr)
  = [.LD .x5 .x10 0, .LD .x6 .x11 0, .ADD .x7 .x5 .x6, .SD .x12 .x7 0]

-- Position independence: no PC-relative instructions.
#guard ((multiReadBody 0 0 [] []).flatten 0 = (multiReadBody 0 0 [] []).flatten 0x80000000)

section Demo

variable (a0 a1 dst : Word) (bs0 bs1 : List (BitVec 8))

/-- A focused read (`LD`) that misses the writable window reads the focused
    read-only region at the pointer register; stated fully resolved (base is
    `rf.get rs1`, matching the `readAt` engine's `⟨rf.get p, _⟩`). -/
private theorem read_engine (roBytes : List (BitVec 8)) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (hofs : signExtend12 ofs = (0 : Word)) (hws : ws.length = 8)
    (hlen : roBytes.length = 8) (hne : rf.get rs1 ≠ rwBase) :
    execBlock ⟨rf.get rs1, roBytes⟩ rwBase rf ws [.LD rd rs1 ofs]
      = (rf.set rd (packBytes roBytes), ws) := by
  have haddr : rf.get rs1 + signExtend12 ofs = rf.get rs1 := by rw [hofs]; bv_omega
  rw [execBlock_cons, execInstrRF]
  dsimp only [aluSem, loadSem]
  rw [if_neg (by
    unfold inRw
    rw [haddr, hws]
    intro hin
    exact hne (by bv_omega))]
  unfold Region.dwordAt
  rw [show ((rf.get rs1 + signExtend12 ofs) - (⟨rf.get rs1, roBytes⟩ : Region).base).toNat = 0
      from by rw [haddr]; bv_omega,
    List.drop_zero, List.take_of_length_le (show roBytes.length ≤ 8 from by omega),
    execBlock_nil]

/-- Address side conditions of a focused read: the load misses the writable
    window (routing to the focused region), and indexes the focused region
    at offset 0, aligned. -/
private theorem read_blockVCs (roBytes : List (BitVec 8)) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (hofs : signExtend12 ofs = (0 : Word)) (hws : ws.length = 8)
    (hlen : roBytes.length = 8) (hne : rf.get rs1 ≠ rwBase) :
    blockVCs ⟨rf.get rs1, roBytes⟩ rwBase rf ws [.LD rd rs1 ofs] := by
  have haddr : rf.get rs1 + signExtend12 ofs = rf.get rs1 := by rw [hofs]; bv_omega
  refine ⟨?_, trivial⟩
  show (if inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8
    then _ else Region.loadOk _ _ _)
  rw [if_neg (by unfold inRw; rw [haddr, hws]; intro hin; exact hne (by bv_omega)), haddr]
  refine ⟨?_, ?_⟩
  · show 8 ∣ ((rf.get rs1 - rf.get rs1 : Word)).toNat
    rw [show ((rf.get rs1 - rf.get rs1 : Word)).toNat = 0 from by bv_omega]
    exact ⟨0, rfl⟩
  · show ((rf.get rs1 - rf.get rs1 : Word)).toNat + 8 ≤ roBytes.length
    rw [show ((rf.get rs1 - rf.get rs1 : Word)).toNat = 0 from by bv_omega]
    omega

/-- The write block's engine run, fully resolved: `x7 := x5 + x6`, the window
    becomes the dword of that sum. -/
private theorem write_engine (rf : RegFile) (ws : List (BitVec 8))
    (hx12 : rf.get .x12 = dst) (hws : ws.length = 8) :
    execBlock Region.empty dst rf ws [.ADD .x7 .x5 .x6, .SD .x12 .x7 0]
      = (rf.set .x7 (rf.get .x5 + rf.get .x6),
          dwordBytes (rf.get .x5 + rf.get .x6)) := by
  have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  rw [execBlock_cons,
    show execInstrRF Region.empty dst rf ws (.ADD .x7 .x5 .x6)
      = (rf.set .x7 (rf.get .x5 + rf.get .x6), ws) from rfl]
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0
    (by
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx12, hs0]
      bv_omega)]
  rw [RegFile.get_set_self _ _ _ (by decide), execBlock_nil,
    setBytes_dword_full _ _ hws]

/-- Address side conditions of the write block: the store fits the writable
    window at offset 0, aligned. -/
private theorem write_blockVCs (rf : RegFile) (ws : List (BitVec 8))
    (hx12 : rf.get .x12 = dst) (hws : ws.length = 8) :
    blockVCs Region.empty dst rf ws [.ADD .x7 .x5 .x6, .SD .x12 .x7 0] := by
  have haddr : (((rf.set .x7 (rf.get .x5 + rf.get .x6)).get .x12
      + signExtend12 (0 : BitVec 12)) - dst).toNat = 0 := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx12,
      show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    bv_omega
  simp only [blockVCs, loadSem, storeSem, aluSem, execInstrRF, inRw, haddr]
  refine ⟨trivial, ⟨?_, ⟨0, rfl⟩⟩, trivial⟩
  omega

/-- **The two-read-only-region triple.**  Hypotheses: the writable window is
    well-formed (`hrw`), both read buffers are well-formed 8-byte regions
    (`hro0`/`hro1`, `hbs0`/`hbs1`), and each read pointer misses the writable
    window (`hne0`/`hne1` — the routing disjointness; regions that actually
    overlapped would make the precondition unsatisfiable via `**`).  Note
    NO `a0 ≠ a1` hypothesis: the two reads may target the same buffer (a
    squaring) or different buffers (a product). -/
theorem multiReadFn_spec (base : Word)
    (hrw : RwRegion.wf ⟨dst, 8⟩)
    (hro0 : Region.wf ⟨a0, bs0⟩) (hro1 : Region.wf ⟨a1, bs1⟩)
    (hbs0 : bs0.length = 8) (hbs1 : bs1.length = 8)
    (hne0 : a0 ≠ dst) (hne1 : a1 ≠ dst) :
    (multiReadFn a0 a1 dst bs0 bs1).Spec base := by
  have hofs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case multiRead.readA0.focus =>
    rintro rf ws A ⟨hx10, hx11, hx12, hA⟩ hApc hp hhp
    refine ⟨bs0, bytesRegion a1 bs1, ⟨hx10, rfl, rfl⟩, ?_, bytesRegion_pcFree _ _, ?_⟩
    · rw [hx10]; rw [hA] at hhp; exact hhp
    · rw [hx10]; exact hro0
  case multiRead.readA0.mem =>
    rintro rf ws A robytes rest hws ⟨hx10, hx11, hx12, hA⟩ ⟨hptr, hrob, hrest⟩ hsat
    have hws8 : ws.length = 8 := hws
    exact read_blockVCs robytes dst rf ws .x5 .x10 0 hofs0 hws8
      (by rw [hrob]; exact hbs0) (by rw [hptr]; exact hne0)
  case multiRead.readA1.focus =>
    rintro rf ws A hreach hApc hp hhp
    -- reach = sp readA0 pre; recover the pinned pointers and ambient shape
    obtain ⟨rf₀, ws₀, A₀, rob0, rest0, hlen₀, ⟨hx10, hx11, hx12, hA⟩,
      hsat0, ⟨hptr0, hrob0, hrest0⟩, hrf, hwsE, hAeq⟩ := hreach
    dsimp only [multiReadFn] at hrf hlen₀
    have hlr0 : rob0.length = 8 := by rw [hrob0]; exact hbs0
    have hws0 : ws₀.length = 8 := hlen₀
    have hx11' : rf.get .x11 = a1 := by
      rw [hrf, read_engine rob0 dst rf₀ ws₀ .x5 .x10 0 hofs0 hws0 hlr0
          (by rw [hx10]; exact hne0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      exact hx11
    have hAeq' : A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1) := by
      rw [hAeq, hrob0, hrest0, hx10]
    refine ⟨bs1, bytesRegion a0 bs0, ⟨hx11', rfl, rfl⟩, ?_, bytesRegion_pcFree _ _, ?_⟩
    · rw [hx11']
      rw [hAeq'] at hhp
      xperm_hyp hhp
    · rw [hx11']; exact hro1
  case multiRead.readA1.mem =>
    rintro rf ws A robytes rest hws hreach ⟨hptr, hrob, hrest⟩ hsat
    have hws8 : ws.length = 8 := hws
    exact read_blockVCs robytes dst rf ws .x6 .x11 0 hofs0 hws8
      (by rw [hrob]; exact hbs1) (by rw [hptr]; exact hne1)
  case multiRead.write.mem =>
    rintro rf ws A hws hreach
    have hws8 : ws.length = 8 := hws
    -- recover x12 = dst through the two focus blocks
    obtain ⟨rf₁, ws₁, A₁, rob1, rest1, hlen1, hreach0, hsat1,
      ⟨hptr1, hrob1, hrest1⟩, hrf1, hws1, hAeq1⟩ := hreach
    obtain ⟨rf₀, ws₀, A₀, rob0, rest0, hlen0, ⟨hx10, hx11, hx12, hA⟩,
      hsat0, ⟨hptr0, hrob0, hrest0⟩, hrf0, hws0, hAeq0⟩ := hreach0
    dsimp only [multiReadFn] at hrf1 hrf0 hlen0 hlen1 ⊢
    have hlr0 : rob0.length = 8 := by rw [hrob0]; exact hbs0
    have hlr1 : rob1.length = 8 := by rw [hrob1]; exact hbs1
    have hws08 : ws₀.length = 8 := hlen0
    have hws18 : ws₁.length = 8 := hlen1
    have hx12' : rf.get .x12 = dst := by
      rw [hrf1, read_engine rob1 dst rf₁ ws₁ .x6 .x11 0 hofs0 hws18 hlr1
          (by rw [hptr1]; exact hne1),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6), hrf0,
        read_engine rob0 dst rf₀ ws₀ .x5 .x10 0 hofs0 hws08 hlr0
          (by rw [hx10]; exact hne0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]
      exact hx12
    exact write_blockVCs dst rf ws hx12' hws8
  case multiRead.post =>
    rintro rf' ws' A''
      ⟨rfW, wsW, hlenW, hreachW, hrf', hws'⟩
    -- outer: the write block; inner: readA1 then readA0
    obtain ⟨rf₁, ws₁, A₁, rob1, rest1, hlen1, hreach0, hsat1,
      ⟨hptr1, hrob1, hrest1⟩, hrf1, hws1, hAeq1⟩ := hreachW
    obtain ⟨rf₀, ws₀, A₀, rob0, rest0, hlen0, ⟨hx10, hx11, hx12, hA⟩,
      hsat0, ⟨hptr0, hrob0, hrest0⟩, hrf0, hws0, hAeq0⟩ := hreach0
    dsimp only [multiReadFn] at hrf1 hrf0 hlen0 hlen1 hrf' hws'
    have hlr0 : rob0.length = 8 := by rw [hrob0]; exact hbs0
    have hlr1 : rob1.length = 8 := by rw [hrob1]; exact hbs1
    have hws08 : ws₀.length = 8 := hlen0
    have hws18 : ws₁.length = 8 := hlen1
    -- fully resolve the register file after both reads
    have hrfW : rfW = (rf₀.set .x5 (packBytes rob0)).set .x6 (packBytes rob1) := by
      rw [hrf1, read_engine rob1 dst rf₁ ws₁ .x6 .x11 0 hofs0 hws18 hlr1
          (by rw [hptr1]; exact hne1), hrf0,
        read_engine rob0 dst rf₀ ws₀ .x5 .x10 0 hofs0 hws08 hlr0
          (by rw [hx10]; exact hne0)]
    have hx12W : rfW.get .x12 = dst := by
      rw [hrfW, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5)]
      exact hx12
    have hx5W : rfW.get .x5 = packBytes rob0 := by
      rw [hrfW, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide)]
    have hx6W : rfW.get .x6 = packBytes rob1 := by
      rw [hrfW, RegFile.get_set_self _ _ _ (by decide)]
    have hwsW8 : wsW.length = 8 := by
      rw [hws1, execBlock_ws_length, hws0, execBlock_ws_length]; exact hws08
    -- run the write block
    rw [write_engine dst rfW wsW hx12W hwsW8] at hrf' hws'
    subst hrf' hws'
    refine ⟨?_, ?_, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7)]; exact hx12W
    · rw [hx5W, hx6W, hrob0, hrob1]
    · rw [hAeq1, hptr1, hrob1, hrest1]; xperm
end Demo


end MultiRead

end SAsm
end EvmAsm.Rv64
