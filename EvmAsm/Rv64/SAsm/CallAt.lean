/-
  EvmAsm.Rv64.SAsm.CallAt

  Demo of `Stmt.callAt`: the callee analogue of `readAt`.  A caller with a
  single primary `region`/`rw` calls a leaf routine TWICE, each call reading
  from a different independent external buffer held as an ambient
  `bytesRegion` atom — the exact shape `CalleesIn` rejects for a plain `call`
  (which requires every callee's `region` to equal the caller's single
  `reg`) and the wall `bnfMulModP`/`secfMulModP` hit (they call
  `bnf_be_to_le(a0)` then `bnf_be_to_le(a1)` with `a0`, `a1` arbitrary
  independent pointers).

  `callAt lbl roR f` focuses one ambient `bytesRegion` atom as the region the
  wrapped callee `f` sees, for the duration of that one call; the enclosing
  `reg` and the remainder of the ambient are framed and restored after.  It
  flattens to the same single `JAL` as `call` (byte-transparent), so a real
  routine wrapping its converter calls this way stays byte-identical.

  The demo callee `adderFn` is a genuine leaf (reads its focused buffer and
  the writable window, writes their sum back; no sub-calls, empty ambient).
  `callAtFn` calls it on `a0` then `a1` (allowed to coincide — a squaring —
  or differ), and its post pins the window to `packBytes bs0 + packBytes bs1`
  — a function of BOTH inputs.  GLM wraps the three converter calls of
  `bnfMulModP` the same way to finish it byte-identically.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64

namespace SAsm

namespace CallAt

open Stmt

/-- The leaf accumulator callee body: read the dword at `x10` (its read-only
    region), read the current window dword at `x11`, write their sum back. -/
def adderBody : List Instr :=
  [.LD .x5 .x10 0, .LD .x6 .x11 0, .ADD .x7 .x5 .x6, .SD .x11 .x7 0]

/-- The leaf accumulator callee.  Read-only region `⟨src, bs⟩`, writable
    window `⟨dst, 8⟩` holding `acc`; result window holds `acc + packBytes bs`.
    Preserves `x11` (the window pointer) and `x13` (`other` — the *other*
    buffer's pointer, which must survive for the caller's second call).
    Empty ambient (a leaf touches no recursive-predicate memory). -/
def adderFn (src dst other : Word) (bs : List (BitVec 8)) (acc : Word) : Fn where
  name := "adder"
  region := ⟨src, bs⟩
  rw := ⟨dst, 8⟩
  pre := fun rf ws A =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ rf.get .x13 = other ∧
    ws = dwordBytes acc ∧ A = empAssertion
  post := fun rf ws A =>
    rf.get .x11 = dst ∧ rf.get .x13 = other ∧
    ws = dwordBytes (acc + packBytes bs) ∧ A = empAssertion
  body := .block "acc" adderBody

section Adder

variable (src dst other : Word) (bs : List (BitVec 8)) (acc : Word)

/-- The accumulator body's engine run, fully resolved. -/
private theorem adder_engine (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst)
    (hws : ws = dwordBytes acc) (hbs : bs.length = 8) (hne : src ≠ dst) :
    execBlock ⟨src, bs⟩ dst rf ws adderBody
      = (((rf.set .x5 (packBytes bs)).set .x6 acc).set .x7 (packBytes bs + acc),
          dwordBytes (packBytes bs + acc)) := by
  have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hwslen : ws.length = 8 := by rw [hws, length_dwordBytes]
  -- LD x5 x10 0 : misses the window, reads the region dword `packBytes bs`
  have hmiss : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 := by
    unfold inRw
    rw [hx10, hs0, hwslen]
    intro hin
    exact hne (by bv_omega)
  rw [show adderBody = [.LD .x5 .x10 0, .LD .x6 .x11 0, .ADD .x7 .x5 .x6, .SD .x11 .x7 0]
      from rfl, execBlock_cons, execInstrRF]
  dsimp only [aluSem, loadSem]
  rw [if_neg hmiss]
  rw [show Region.dwordAt ⟨src, bs⟩ (rf.get .x10 + signExtend12 (0 : BitVec 12))
        = packBytes bs from by
      unfold Region.dwordAt
      rw [hx10, hs0, show ((src + (0 : Word)) - src).toNat = 0 from by bv_omega,
        List.drop_zero, List.take_of_length_le (show bs.length ≤ 8 from by omega)]]
  -- LD x6 x11 0 : hits the window, reads `acc`
  rw [execBlock_cons, execInstrRF]
  dsimp only [aluSem, loadSem]
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
  rw [if_pos (show inRw dst ws (rf.get .x11 + signExtend12 (0 : BitVec 12)) 8 from by
    unfold inRw; rw [hx11, hs0, hwslen]; bv_omega)]
  rw [show Region.dwordAt ⟨dst, ws⟩ (rf.get .x11 + signExtend12 (0 : BitVec 12)) = acc from by
    unfold Region.dwordAt
    rw [hx11, hs0, show ((dst + (0 : Word)) - dst).toNat = 0 from by bv_omega,
      List.drop_zero, List.take_of_length_le (show ws.length ≤ 8 from by omega), hws,
      packBytes_dwordBytes]]
  -- ADD x7 x5 x6
  rw [execBlock_cons, execInstrRF]
  dsimp only [aluSem]
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
    RegFile.get_set_self _ _ _ (by decide)]
  -- SD x11 x7 0
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ 0 (by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11, hs0]
    bv_omega)]
  rw [RegFile.get_set_self _ _ _ (by decide), execBlock_nil,
    setBytes_dword_full _ _ hwslen]

/-- Address side conditions of the accumulator block. -/
private theorem adder_blockVCs (rf : RegFile) (ws : List (BitVec 8))
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst)
    (hws : ws = dwordBytes acc) (hbs : bs.length = 8) (hne : src ≠ dst) :
    blockVCs ⟨src, bs⟩ dst rf ws adderBody := by
  have hs0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hwslen : ws.length = 8 := by rw [hws, length_dwordBytes]
  have hmiss : ¬ inRw dst ws (rf.get .x10 + signExtend12 (0 : BitVec 12)) 8 := by
    unfold inRw; rw [hx10, hs0, hwslen]; intro hin; exact hne (by bv_omega)
  -- per-instruction step results (so the threaded register file reduces)
  have hstep0 : execInstrRF ⟨src, bs⟩ dst rf ws (.LD .x5 .x10 0)
      = (rf.set .x5 (packBytes bs), ws) := by
    unfold execInstrRF; dsimp only [aluSem, loadSem]; rw [if_neg hmiss]
    unfold Region.dwordAt
    rw [hx10, hs0, show ((src + (0 : Word)) - src).toNat = 0 from by bv_omega,
      List.drop_zero, List.take_of_length_le (show bs.length ≤ 8 from by omega)]
  have hx11a : (rf.set .x5 (packBytes bs)).get .x11 = dst := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]; exact hx11
  have hstep1 : execInstrRF ⟨src, bs⟩ dst (rf.set .x5 (packBytes bs)) ws (.LD .x6 .x11 0)
      = ((rf.set .x5 (packBytes bs)).set .x6 acc, ws) := by
    unfold execInstrRF; dsimp only [aluSem, loadSem]
    rw [if_pos (show inRw dst ws
        ((rf.set .x5 (packBytes bs)).get .x11 + signExtend12 (0 : BitVec 12)) 8 from by
      unfold inRw; rw [hx11a, hs0, hwslen]; bv_omega)]
    unfold Region.dwordAt
    rw [hx11a, hs0, show ((dst + (0 : Word)) - dst).toNat = 0 from by bv_omega,
      List.drop_zero, List.take_of_length_le (show ws.length ≤ 8 from by omega), hws,
      packBytes_dwordBytes]
  have hstep2 : execInstrRF ⟨src, bs⟩ dst ((rf.set .x5 (packBytes bs)).set .x6 acc) ws
        (.ADD .x7 .x5 .x6)
      = (((rf.set .x5 (packBytes bs)).set .x6 acc).set .x7 (packBytes bs + acc), ws) := by
    unfold execInstrRF; dsimp only [aluSem]
    rw [RegFile.get_set_self _ _ _ (by decide),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
      RegFile.get_set_self _ _ _ (by decide)]
  have hx11b : (((rf.set .x5 (packBytes bs)).set .x6 acc).set .x7 (packBytes bs + acc)).get .x11
      = dst := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]; exact hx11
  rw [show adderBody = [.LD .x5 .x10 0, .LD .x6 .x11 0, .ADD .x7 .x5 .x6, .SD .x11 .x7 0]
      from rfl]
  simp only [blockVCs, hstep0, hstep1, hstep2, loadSem, storeSem]
  refine ⟨?_, ?_, trivial, ?_, trivial⟩
  · -- LD x5 x10 0 misses the window → reads region
    rw [if_neg hmiss, hx10, hs0]
    refine ⟨?_, ?_⟩
    · show 8 ∣ ((src + (0 : Word)) - src).toNat
      rw [show ((src + (0 : Word)) - src).toNat = 0 from by bv_omega]; exact ⟨0, rfl⟩
    · show ((src + (0 : Word)) - src).toNat + 8 ≤ bs.length
      rw [show ((src + (0 : Word)) - src).toNat = 0 from by bv_omega]; omega
  · -- LD x6 x11 0 hits the window
    rw [if_pos (show inRw dst ws
        ((rf.set .x5 (packBytes bs)).get .x11 + signExtend12 (0 : BitVec 12)) 8 from by
      unfold inRw; rw [hx11a, hs0, hwslen]; bv_omega), hx11a, hs0]
    refine ⟨?_, ?_⟩
    · show 8 ∣ ((dst + (0 : Word)) - dst).toNat
      rw [show ((dst + (0 : Word)) - dst).toNat = 0 from by bv_omega]; exact ⟨0, rfl⟩
    · show ((dst + (0 : Word)) - dst).toNat + 8 ≤ ws.length
      rw [show ((dst + (0 : Word)) - dst).toNat = 0 from by bv_omega]; omega
  · -- SD x11 x7 0 hits the window, aligned
    rw [hx11b, hs0]
    refine ⟨?_, ?_⟩
    · unfold inRw
      rw [show ((dst + (0 : Word)) - dst).toNat = 0 from by bv_omega]; omega
    · show 8 ∣ ((dst + (0 : Word)) - dst).toNat
      rw [show ((dst + (0 : Word)) - dst).toNat = 0 from by bv_omega]; exact ⟨0, rfl⟩

/-- **The leaf callee is verified.**  `src ≠ dst` resolves the region/window
    routing; `hbs` fixes the region width. -/
theorem adderFn_spec (base : Word)
    (hro : Region.wf ⟨src, bs⟩) (hrw : RwRegion.wf ⟨dst, 8⟩)
    (hbs : bs.length = 8) (hne : src ≠ dst) :
    (adderFn src dst other bs acc).Spec base := by
  vcgen
  case region => exact ⟨hro, hrw⟩
  case adder.acc.mem =>
    rintro rf ws A hws ⟨hx10, hx11, hx13, hwsd, hA⟩
    exact adder_blockVCs src dst bs acc rf ws hx10 hx11 hwsd hbs hne
  case adder.post =>
    rintro rf' ws' A'' ⟨rf, ws, hlen, ⟨hx10, hx11, hx13, hwsd, hA⟩, hrf', hws'⟩
    dsimp only [adderFn] at hrf' hws' ⊢
    rw [adder_engine src dst bs acc rf ws hx10 hx11 hwsd hbs hne] at hrf' hws'
    subst hrf' hws' hA
    refine ⟨?_, ?_, ?_, rfl⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5)]
      exact hx11
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x5)]
      exact hx13
    · show dwordBytes (packBytes bs + acc) = dwordBytes (acc + packBytes bs)
      rw [show (packBytes bs + acc : Word) = acc + packBytes bs from by bv_omega]

end Adder

-- ============================================================================
-- The caller: two `callAt` calls to different focused regions
-- ============================================================================

section Caller

/-- The adder body occupies 4 slots; `+ epilogue` fits the address space. -/
private theorem adder_sz (src dst other : Word) (bs : List (BitVec 8)) (acc : Word) :
    4 * ((adderFn src dst other bs acc).body.size + 1) ≤ 2 ^ 64 := by
  show 4 * (4 + 1) ≤ 2 ^ 64; decide

/-- Callee handle for the first buffer (`a0`), at `0x3000`. -/
def adderHandle0 (a0 a1 dst : Word) (bs0 : List (BitVec 8))
    (hro0 : Region.wf ⟨a0, bs0⟩) (hrw : RwRegion.wf ⟨dst, 8⟩)
    (hbs0 : bs0.length = 8) (hne0 : a0 ≠ dst) : FnHandle :=
  (adderFn a0 dst a1 bs0 0).toHandle 0x3000
    (adderFn_spec a0 dst a1 bs0 0 0x3000 hro0 hrw hbs0 hne0) (adder_sz ..)

/-- Callee handle for the second buffer (`a1`), at `0x3200`; its accumulator
    seed is the first buffer's dword, so the result depends on BOTH inputs. -/
def adderHandle1 (a1 dst : Word) (bs0 bs1 : List (BitVec 8))
    (hro1 : Region.wf ⟨a1, bs1⟩) (hrw : RwRegion.wf ⟨dst, 8⟩)
    (hbs1 : bs1.length = 8) (hne1 : a1 ≠ dst) : FnHandle :=
  (adderFn a1 dst a1 bs1 (packBytes bs0)).toHandle 0x3200
    (adderFn_spec a1 dst a1 bs1 (packBytes bs0) 0x3200 hro1 hrw hbs1 hne1) (adder_sz ..)

/-- **The two-focused-call demo function.**  `a0`, `a1` are two independent
    read-only buffers held as ambient `bytesRegion` atoms (allowed to
    coincide); `dst` is the primary writable window.  It calls the adder on
    `a0` (focusing `a0`), moves `a1`'s pointer into the argument register,
    then calls the adder on `a1` (focusing `a1`).  The post pins the window
    to `packBytes bs0 + packBytes bs1` — a function of BOTH inputs. -/
def callAtFn (a0 a1 dst : Word) (bs0 bs1 : List (BitVec 8))
    (hro0 : Region.wf ⟨a0, bs0⟩) (hro1 : Region.wf ⟨a1, bs1⟩)
    (hrw : RwRegion.wf ⟨dst, 8⟩) (hbs0 : bs0.length = 8) (hbs1 : bs1.length = 8)
    (hne0 : a0 ≠ dst) (hne1 : a1 ≠ dst) : Fn where
  name := "callAt"
  region := Region.empty
  rw := ⟨dst, 8⟩
  pre := fun rf ws A =>
    rf.get .x10 = a0 ∧ rf.get .x11 = dst ∧ rf.get .x13 = a1 ∧
    ws = dwordBytes 0 ∧ A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
  post := fun rf ws A =>
    rf.get .x11 = dst ∧
    ws = dwordBytes (packBytes bs0 + packBytes bs1) ∧
    A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
  body :=
    .callAt "cA0" (fun _ _ _ rest => rest = bytesRegion a1 bs1)
        (adderHandle0 a0 a1 dst bs0 hro0 hrw hbs0 hne0) ;;;
    .block "mv" [.MV .x10 .x13] ;;;
    .callAt "cA1" (fun _ _ _ rest => rest = bytesRegion a0 bs0)
        (adderHandle1 a1 dst bs0 bs1 hro1 hrw hbs1 hne1)

/-- Byte-transparency: each `callAt` flattens to exactly one `JAL` — no
    injected instructions, so a real routine wrapping converter calls this
    way stays byte-identical. -/
theorem callAt_byte_transparent (lbl : String)
    (roR : RegFile → List (BitVec 8) → Assertion → Assertion → Prop)
    (f : FnHandle) (addr : Word) :
    (Stmt.callAt lbl roR f).flatten addr
      = [.JAL .x1 (BitVec.setWidth 21 (f.entry - addr))] := rfl

/-- The caller's code requirement: its own flattened body plus both callee
    handles' code — one `union`, no manual disjointness. -/
def callAtCr (a0 a1 dst : Word) (bs0 bs1 : List (BitVec 8))
    (hro0 : Region.wf ⟨a0, bs0⟩) (hro1 : Region.wf ⟨a1, bs1⟩)
    (hrw : RwRegion.wf ⟨dst, 8⟩) (hbs0 : bs0.length = 8) (hbs1 : bs1.length = 8)
    (hne0 : a0 ≠ dst) (hne1 : a1 ≠ dst) : CodeReq :=
  ((CodeReq.ofProg 0x1000
      ((callAtFn a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1).body.flatten 0x1000)).union
    (adderHandle0 a0 a1 dst bs0 hro0 hrw hbs0 hne0).code).union
    (adderHandle1 a1 dst bs0 bs1 hro1 hrw hbs1 hne1).code

/-- **The two-focused-call demo is verified.**  Two `callAt` calls to
    *different* focused regions `a0`, `a1` (the shape a plain `call` rejects),
    with a post depending on BOTH — the `bnfMulModP`/`secfMulModP` template. -/
theorem callAtFn_spec (a0 a1 dst : Word) (bs0 bs1 : List (BitVec 8))
    (hro0 : Region.wf ⟨a0, bs0⟩) (hro1 : Region.wf ⟨a1, bs1⟩)
    (hrw : RwRegion.wf ⟨dst, 8⟩) (hbs0 : bs0.length = 8) (hbs1 : bs1.length = 8)
    (hne0 : a0 ≠ dst) (hne1 : a1 ≠ dst) :
    (callAtFn a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1).SpecR 0x1000
      (callAtCr a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1) := by
  -- handle entries / regions / pre / post, exposed by unfolding
  have hH0e : (adderHandle0 a0 a1 dst bs0 hro0 hrw hbs0 hne0).entry = 0x3000 := rfl
  have hH1e : (adderHandle1 a1 dst bs0 bs1 hro1 hrw hbs1 hne1).entry = 0x3200 := rfl
  -- code containment of the two callees into `cr`
  have hcode0 : ∀ a i, (adderHandle0 a0 a1 dst bs0 hro0 hrw hbs0 hne0).code a = some i →
      callAtCr a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1 a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk5 : kk < 5 := hk
    have hP : CodeReq.ofProg 0x1000
        ((callAtFn a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1).body.flatten 0x1000)
        ((0x3000 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have : k' < 3 := hk'
      bv_omega
    simp only [callAtCr, CodeReq.union, hP, h]
  have hcode1 : ∀ a i, (adderHandle1 a1 dst bs0 bs1 hro1 hrw hbs1 hne1).code a = some i →
      callAtCr a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1 a = some i := by
    intro a i h
    obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
    have hk5 : kk < 5 := hk
    have hP : CodeReq.ofProg 0x1000
        ((callAtFn a0 a1 dst bs0 bs1 hro0 hro1 hrw hbs0 hbs1 hne0 hne1).body.flatten 0x1000)
        ((0x3200 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have : k' < 3 := hk'
      bv_omega
    have hA0 : (adderHandle0 a0 a1 dst bs0 hro0 hrw hbs0 hne0).code
        ((0x3200 : Word) + BitVec.ofNat 64 (4 * kk)) = none := by
      show CodeReq.ofProg 0x3000 (_) ((0x3200 : Word) + BitVec.ofNat 64 (4 * kk)) = none
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have : k' < 5 := hk'
      bv_omega
    simp only [callAtCr, CodeReq.union, hP, hA0, h]
  show Fn.SpecR _ _ _
  vcgen
  case region => exact ⟨Region.empty_wf, hrw⟩
  case code =>
    intro a i h
    simp only [callAtCr, CodeReq.union, h]
  case callees =>
    refine ⟨⟨hcode0, rfl⟩, trivial, hcode1, rfl⟩
  case calls =>
    refine ⟨⟨?_, ?_, ?_⟩, trivial, ?_, ?_, ?_⟩
    · rw [hH0e]; decide
    · decide
    · apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have : k' < 5 := hk'
      bv_omega
    · simp only [Stmt.size, List.length_cons, List.length_nil]; rw [hH1e]; decide
    · simp only [Stmt.size, List.length_cons, List.length_nil]; decide
    · simp only [Stmt.size, List.length_cons, List.length_nil]
      apply CodeReq.ofProg_none_range
      intro k' hk' heq
      have : k' < 5 := hk'
      bv_omega
  case callAt.cA0.focus =>
    rintro rf ws A ⟨hx10, hx11, hx13, hwsd, hA⟩ hApc hp hhp
    refine ⟨bytesRegion a1 bs1, rfl, ?_, bytesRegion_pcFree _ _⟩
    show (bytesRegion a0 bs0 ** bytesRegion a1 bs1) hp
    rw [hA] at hhp; exact hhp
  case callAt.cA0.pre =>
    rintro rf ws A rest hws ⟨hx10, hx11, hx13, hwsd, hA⟩ hrest
    exact ⟨hx10, hx11, hx13, hwsd, rfl⟩
  case callAt.cA0.post_emp =>
    rintro rf ws A ⟨hx11, hx13, hwsd, hA⟩
    exact hA
  case callAt.cA1.focus =>
    rintro rf ws A hreach hApc hp hhp
    -- reach = sp mv (sp cA0 pre); recover A = a0-region ** a1-region
    obtain ⟨rf1, ws1, hlen1, hcA0, hrfmv, hwsmv⟩ := hreach
    obtain ⟨rf0, ws0, A0, rest0, hlen0, ⟨hx10, hx11, hx13, hwsd, hA0⟩,
      -, hrest0, hpost0, hAeq⟩ := hcA0
    subst hrest0
    refine ⟨bytesRegion a0 bs0, rfl, ?_, bytesRegion_pcFree _ _⟩
    show (bytesRegion a1 bs1 ** bytesRegion a0 bs0) hp
    have hAeq' : A = (bytesRegion a0 bs0 ** bytesRegion a1 bs1) := by
      rw [hAeq]; rfl
    rw [hAeq'] at hhp
    xperm_hyp hhp
  case callAt.cA1.pre =>
    rintro rf ws A rest hws hreach hrest
    obtain ⟨rf1, ws1, hlen1, hcA0, hrfmv, hwsmv⟩ := hreach
    obtain ⟨rf0, ws0, A0, rest0, hlen0, ⟨hx10, hx11, hx13, hwsd, hA0⟩,
      -, hrest0, hpost0, hAeq⟩ := hcA0
    obtain ⟨hx11', hx13', hws1', hemp⟩ := hpost0
    -- after cA0: rf1.get x11 = dst, x13 = a1, ws1 = dwordBytes (packBytes bs0);
    -- mv sets x10 := rf1.get x13 = a1, ws unchanged
    have hmv : rf = rf1.set .x10 (rf1.get .x13) := by rw [hrfmv]; rfl
    refine ⟨?_, ?_, ?_, ?_, rfl⟩
    · rw [hmv, RegFile.get_set_self _ _ _ (by decide)]; exact hx13'
    · rw [hmv, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10)]; exact hx11'
    · rw [hmv, RegFile.get_set_ne _ _ _ _ (by decide : Reg.x13 ≠ .x10)]; exact hx13'
    · rw [hwsmv]
      show ws1 = dwordBytes (packBytes bs0)
      rw [hws1']; congr 1; bv_omega
  case callAt.cA1.post_emp =>
    rintro rf ws A ⟨hx11, hx13, hwsd, hA⟩
    exact hA
  case callAt.post =>
    rintro rf' ws' A''
      ⟨rf1, ws1, A1, rest1, hlen1, hmvReach, -, hrest1, hpost1, hAeq1⟩
    obtain ⟨hx11p, hx13p, hws1eq, -⟩ := hpost1
    subst hrest1
    refine ⟨hx11p, ?_, ?_⟩
    · exact hws1eq
    · show A'' = (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
      rw [hAeq1]
      show (bytesRegion a1 bs1 ** bytesRegion a0 bs0) = _
      xperm

end Caller

end CallAt

end SAsm
end EvmAsm.Rv64
