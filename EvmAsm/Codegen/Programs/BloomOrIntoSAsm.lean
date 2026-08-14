/-
  EvmAsm.Codegen.Programs.BloomOrIntoSAsm

  Verified SAsm port of `bloom_or_into` (bead evm-asm-4ch8f.20): OR one
  256-byte bloom filter (`src`, a1) into another (`dst`, a0), in place, a
  dword at a time (32 iterations of `LD dst; LD src; OR; SD dst`).

  Post: the destination bloom becomes the **pointwise OR** of its original
  contents and the source — `dst[j] = dst₀[j] ||| src[j]` for every one of
  the 256 bytes.  This is the Ethereum block/receipt bloom accumulation
  (a dword `|||` is the byte-wise `|||` of its eight bytes).

  Structure: a top-tested `«while»` (the emitted `BEQ x5,x0 → exit; body;
  JAL back` shape) wrapped by a prologue block (`x5 := 32; x6 := dst;
  x7 := src`) and an epilogue block (`x10 := 0`, the return value).  The
  destination is the primary read-write region (read AND written — RMW);
  the source is the read-only `region`.

  Byte-identity: the structured flatten is pinned byte-for-byte against the
  emitted `bloomOrInto_prog` (Bloom.lean).  Spec-only module — no EEST A/B.
-/

import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Rv64.SAsm.FnFlat

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace BloomOrIntoSAsm

/-! ## Pointwise-OR primitives -/

/-- Byte extraction commutes with `|||` (bitwise OR is per-byte). -/
theorem extractByte_or (a b : Word) (k : Nat) :
    extractByte (a ||| b) k = extractByte a k ||| extractByte b k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_or]
  by_cases h : i < 8 <;> simp [h]

/-- Reading byte `k < 8` of the length-8 window `(L.drop a).take 8` is the
    total lookup `L.getD (a + k) 0`. -/
theorem getByteAt_dropTake (L : List (BitVec 8)) (a k : Nat) (hk : k < 8) :
    getByteAt ((L.drop a).take 8) k = L.getD (a + k) 0 := by
  unfold getByteAt
  by_cases hlt : k < ((L.drop a).take 8).length
  · rw [dif_pos hlt, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by
        simp only [List.length_take, List.length_drop] at hlt; omega),
      Option.getD_some]
  · rw [dif_neg hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      simp only [List.length_take, List.length_drop] at hlt ⊢; omega), Option.getD_none]

/-- The `k`-th output byte of the OR loop: original dst byte OR source byte. -/
def orByte (src orig : List (BitVec 8)) (k : Nat) : BitVec 8 :=
  orig.getD k 0 ||| src.getD k 0

/-- `dwordBytes` as a `map` of `extractByte` over `range 8`. -/
theorem dwordBytes_eq_map (v : Word) :
    dwordBytes v = (List.range 8).map (extractByte v) := by rfl

/-- The eight bytes of the stored dword `packBytes origCell ||| packBytes
    srcCell` (cell `i`) are exactly the pointwise ORs `orByte src orig
    (8*i + ·)`. -/
theorem dwordBytes_or_slice (src orig : List (BitVec 8)) (i : Nat) :
    dwordBytes (packBytes ((orig.drop (8 * i)).take 8)
        ||| packBytes ((src.drop (8 * i)).take 8))
      = (List.range 8).map (fun k => orByte src orig (8 * i + k)) := by
  rw [dwordBytes_eq_map]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [extractByte_or, extractByte_packBytes_total _ k hk, extractByte_packBytes_total _ k hk,
    getByteAt_dropTake _ _ _ hk, getByteAt_dropTake _ _ _ hk]
  rfl

/-! ## The OR loop window -/

/-- Loop window after `i` dwords OR'd: the first `8*i` bytes are the pointwise
    OR, the rest is the untouched tail of the original dst bloom. -/
def orWin (src orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  (List.range (8 * i)).map (orByte src orig) ++ orig.drop (8 * i)

theorem orWin_zero (src orig : List (BitVec 8)) : orWin src orig 0 = orig := by
  simp [orWin]

theorem length_orWin (src orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 256) (hi : i ≤ 32) : (orWin src orig i).length = 256 := by
  simp only [orWin, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

/-- `List.range (8*(i+1))` splits after the first `8*i` entries into the eight
    cell indices `8*i + k`. -/
theorem map_orByte_range_succ (src orig : List (BitVec 8)) (i : Nat) :
    (List.range (8 * (i + 1))).map (orByte src orig)
      = (List.range (8 * i)).map (orByte src orig)
        ++ (List.range 8).map (fun k => orByte src orig (8 * i + k)) := by
  rw [show 8 * (i + 1) = 8 * i + 8 from by omega, List.range_add, List.map_append,
    List.map_map]
  rfl

/-- One dword step: splicing cell `i`'s stored dword advances the window from
    `i` to `i+1`. -/
theorem orWin_step (src orig : List (BitVec 8)) (i : Nat)
    (h : orig.length = 256) (hi : i < 32) :
    setBytes (orWin src orig i) (8 * i)
        (dwordBytes (packBytes ((orig.drop (8 * i)).take 8)
          ||| packBytes ((src.drop (8 * i)).take 8)))
      = orWin src orig (i + 1) := by
  have hpre : ((List.range (8 * i)).map (orByte src orig)).length = 8 * i := by simp
  have htk8 : ((orig.drop (8 * i)).take 8).length = 8 := by
    rw [List.length_take, List.length_drop, h]; omega
  -- A dword store at offset 0 of `orig.drop (8*i)` (abstracted over the stored
  -- word `V` so the split does not disturb the CELL that mentions `orig.drop`).
  have hsub : ∀ V : Word,
      setBytes (orig.drop (8 * i)) 0 (dwordBytes V)
        = dwordBytes V ++ (orig.drop (8 * i)).drop 8 := by
    intro V
    conv_lhs => rw [show orig.drop (8 * i)
        = (orig.drop (8 * i)).take 8 ++ (orig.drop (8 * i)).drop 8 from
        (List.take_append_drop 8 _).symm]
    rw [setBytes_append_left _ _ _ _ (by simp [htk8]), setBytes_dword_full _ _ htk8]
  simp only [orWin]
  rw [setBytes_append_right _ _ _ _ hpre.le, hpre, Nat.sub_self, hsub,
    dwordBytes_or_slice, List.drop_drop, ← List.append_assoc, ← map_orByte_range_succ,
    show 8 * i + 8 = 8 * (i + 1) from by omega]

/-- At `i = 32` the whole window is the pointwise OR of all 256 bytes. -/
theorem orWin_full (src orig : List (BitVec 8)) (h : orig.length = 256) :
    orWin src orig 32 = (List.range 256).map (orByte src orig) := by
  rw [orWin, show 8 * 32 = 256 from by norm_num, List.drop_eq_nil_of_le (by rw [h]),
    List.append_nil]

/-! ## The `bloom_or_into` SAsm function -/

/-- Prologue: `x5 := 32` (dword count), `x6 := dst` (a0), `x7 := src` (a1). -/
def proBlock : List Instr := [.LI .x5 (32 : Word), .MV .x6 .x10, .MV .x7 .x11]

/-- One dword OR step: load dst cell, load src cell, OR, store dst cell,
    advance both cursors by 8, decrement the count. -/
def orStepBlock : List Instr :=
  [.LD .x28 .x6 (0 : BitVec 12), .LD .x29 .x7 (0 : BitVec 12),
   .OR .x28 .x28 .x29, .SD .x6 .x28 (0 : BitVec 12),
   .ADDI .x6 .x6 (8 : BitVec 12), .ADDI .x7 .x7 (8 : BitVec 12),
   .ADDI .x5 .x5 (-1 : BitVec 12)]

/-- Epilogue: `x10 := 0` (the routine returns 0). -/
def epiBlock : List Instr := [.LI .x10 (0 : Word)]

/-- Loop invariant after `i` dwords: cursors at `+8*i`, count `32-i`, and the
    dst working set is the `i`-dword OR window. -/
def bloomOrInv (src dst : Word) (srcBytes orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws A =>
    rf.get .x5 = BitVec.ofNat 64 (32 - i) ∧
    rf.get .x6 = dst + BitVec.ofNat 64 (8 * i) ∧
    rf.get .x7 = src + BitVec.ofNat 64 (8 * i) ∧
    i ≤ 32 ∧ srcBytes.length = 256 ∧ orig.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) ∧
    ws = orWin srcBytes orig i ∧ A = empAssertion

/-- `bloom_or_into` body: prologue ; the 32-iteration dword OR loop ; epilogue. -/
def bloomOrBody (src dst : Word) (srcBytes orig : List (BitVec 8)) : Stmt :=
  .block "pro" proBlock ;;;
  .«while» "loop" (.bne .x5 .x0) 32 (bloomOrInv src dst srcBytes orig)
    (.block "step" orStepBlock) ;;;
  .block "epi" epiBlock

/-- `bloom_or_into` as a verified SAsm `Fn`: src is the read-only region, dst
    the read-write region (RMW).  Post: dst = pointwise OR of dst₀ and src. -/
def bloomOrIntoFn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "bloomOrInto"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 256⟩
  pre := fun rf ws A =>
    rf.get .x10 = dst ∧ rf.get .x11 = src ∧
    ws = orig ∧ orig.length = 256 ∧ srcBytes.length = 256 ∧
    src.toNat + 256 < 2 ^ 64 ∧ dst.toNat + 256 < 2 ^ 64 ∧
    (src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat) ∧
    A = empAssertion
  post := fun rf ws A =>
    rf.get .x10 = 0 ∧ ws = (List.range 256).map (orByte srcBytes orig) ∧
    A = empAssertion
  body := bloomOrBody src dst srcBytes orig

/-! ## The correctness triple -/

/-- Dropping the first `8*i` bytes of the `i`-window discards the OR'd prefix
    and exposes the untouched original tail. -/
theorem orWin_drop (src orig : List (BitVec 8)) (i : Nat) :
    (orWin src orig i).drop (8 * i) = orig.drop (8 * i) := by
  have h : ((List.range (8 * i)).map (orByte src orig)).length = 8 * i := by simp
  rw [orWin, List.drop_append_of_le_length (le_of_eq h.symm),
    List.drop_eq_nil_of_le (le_of_eq h), List.nil_append]

/-- An `LD` that misses the writable window reads the read-only region
    (dword form; local reprove of `MultiRw`'s private lemma). -/
theorem ld_dword_romiss (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12) (v : Word)
    (hmiss : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8)
    (hv : ro.dwordAt (rf.get rs1 + signExtend12 ofs) = v) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs) = (rf.set rd v, ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg hmiss, hv]

/-- Register file after one dword OR step (given the loaded dst dword `vdst`
    and src dword `vsrc`): `x28 := vdst ||| vsrc`, both cursors `+8`, count `-1`. -/
def orStepRf (rf : RegFile) (vdst vsrc : Word) : RegFile :=
  ((((rf.set .x28 vdst).set .x29 vsrc).set .x28 (vdst ||| vsrc)).set .x6
        (rf.get .x6 + signExtend12 (8 : BitVec 12))).set .x7
        (rf.get .x7 + signExtend12 (8 : BitVec 12)) |>.set .x5
        (rf.get .x5 + signExtend12 (-1 : BitVec 12))

theorem orStepRf_get_x5 (rf : RegFile) (vdst vsrc : Word) :
    (orStepRf rf vdst vsrc).get .x5 = rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
  unfold orStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x5 ≠ .x0)]

theorem orStepRf_get_x6 (rf : RegFile) (vdst vsrc : Word) :
    (orStepRf rf vdst vsrc).get .x6 = rf.get .x6 + signExtend12 (8 : BitVec 12) := by
  unfold orStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0)]

theorem orStepRf_get_x7 (rf : RegFile) (vdst vsrc : Word) :
    (orStepRf rf vdst vsrc).get .x7 = rf.get .x7 + signExtend12 (8 : BitVec 12) := by
  unfold orStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5),
    RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0)]

/-- **The dword OR-step engine** (own heartbeat budget): one loop body loads
    the dst cell (RW), loads the src cell (RO miss), ORs them, stores the
    result back into the dst cell, and advances both cursors + the count. -/
theorem or_step_engine (src dst : Word) (i : Nat) (srcBytes : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 (8 * i))
    (hx7 : rf.get .x7 = src + BitVec.ofNat 64 (8 * i))
    (hi : i < 32)
    (hsrc : src.toNat + 256 < 2 ^ 64) (hdst : dst.toNat + 256 < 2 ^ 64)
    (hdisj : src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)
    (hws : ws.length = 256) :
    execBlock ⟨src, srcBytes⟩ dst rf ws orStepBlock
      = (orStepRf rf (packBytes ((ws.drop (8 * i)).take 8))
            (packBytes ((srcBytes.drop (8 * i)).take 8)),
         setBytes ws (8 * i)
           (dwordBytes (packBytes ((ws.drop (8 * i)).take 8)
             ||| packBytes ((srcBytes.drop (8 * i)).take 8)))) := by
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hi8 : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i := by
    rw [BitVec.toNat_ofNat]; omega
  -- dst LD address: offset `8*i` into the writable window
  have hdst_addr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [hx6, hse_0]; bv_omega
  -- src LD address (register x7 survives the first load into x28)
  have hx7' : (rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).get .x7
      + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 (8 * i) := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx7, hse_0]; simp
  -- the src LD misses the writable window (disjointness)
  have hmiss : ¬ inRw dst ws
      ((rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).get .x7
        + signExtend12 (0 : BitVec 12)) 8 := by
    rw [hx7']; unfold inRw; rw [hws]
    have hsubd : (src + BitVec.ofNat 64 (8 * i) - dst).toNat
        = (src.toNat + 8 * i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi8]; congr 1; omega
    rw [hsubd]; rcases hdisj with hd | hd <;> omega
  -- the src cell read from the read-only region
  have hsrcval : Region.dwordAt ⟨src, srcBytes⟩
      ((rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).get .x7
        + signExtend12 (0 : BitVec 12))
      = packBytes ((srcBytes.drop (8 * i)).take 8) := by
    rw [hx7']
    show packBytes ((srcBytes.drop ((src + BitVec.ofNat 64 (8 * i) - src).toNat)).take 8)
      = packBytes ((srcBytes.drop (8 * i)).take 8)
    rw [show (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi8]; omega]
  rw [show orStepBlock = [.LD .x28 .x6 (0 : BitVec 12), .LD .x29 .x7 (0 : BitVec 12),
      .OR .x28 .x28 .x29, .SD .x6 .x28 (0 : BitVec 12),
      .ADDI .x6 .x6 (8 : BitVec 12), .ADDI .x7 .x7 (8 : BitVec 12),
      .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
  -- LD dst (writable window, offset 8*i)
  rw [execBlock_cons, execInstrRF_ld_dword _ _ _ _ _ _ _ (8 * i)
      (packBytes ((ws.drop (8 * i)).take 8)) hdst_addr (by rw [hws]; omega) rfl]
  dsimp only
  -- LD src (read-only region)
  rw [execBlock_cons, ld_dword_romiss _ _ _ _ _ _ _
      (packBytes ((srcBytes.drop (8 * i)).take 8)) hmiss hsrcval]
  dsimp only
  -- OR
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x29 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x28 ≠ .x29),
    RegFile.get_set_self _ _ _ (by decide : Reg.x28 ≠ .x0)]
  -- SD dst (writable window, offset 8*i)
  have hstore_addr : ((((rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).set .x29
        (packBytes ((srcBytes.drop (8 * i)).take 8))).set .x28
        (packBytes ((ws.drop (8 * i)).take 8) ||| packBytes ((srcBytes.drop (8 * i)).take 8))).get .x6
        + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
    rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
      RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hx6, hse_0]
    bv_omega
  rw [execBlock_cons, execInstrRF_sd_dword _ _ _ _ _ _ _ (8 * i) hstore_addr]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x28 ≠ .x0)]
  -- three ADDIs
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  -- align the register file with `orStepRf`
  unfold orStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x29),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x29)]

/-- **The `bloom_or_into` correctness triple.** -/
theorem bloomOrIntoFn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 256⟩) (base : Word) :
    (bloomOrIntoFn src dst srcBytes orig).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case bloomOrInto.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, hlen₀,
      ⟨hx10, hx11, rfl, hol', hsl', hsrcb, hdstb, hdisjb, hA⟩, rfl, rfl⟩
    simp only [proBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, by omega, hsl', hol', hsrcb, hdstb, hdisjb, ?_, hA⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide : Reg.x5 ≠ .x0)]
      rfl
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), hx10]
      simp
    · rw [RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
    · rw [orWin_zero]
  case bloomOrInto.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, hlen₀,
      ⟨⟨hx5, hx6, hx7, hile, hslI, holI, hsrcI, hdstI, hdisjI, hwin, hAI⟩, hcond⟩,
        rfl, rfl⟩
    have hwslen : ws₀.length = 256 := by
      rw [hwin]; exact length_orWin srcBytes orig i holI (by omega)
    simp only [show (bloomOrIntoFn src dst srcBytes orig).rw.base = dst from rfl,
      show (bloomOrIntoFn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl]
    rw [or_step_engine src dst i srcBytes rf₀ ws₀ hx6 hx7 hi hsrcI hdstI hdisjI hwslen]
    refine ⟨?_, ?_, ?_, by omega, hslI, holI, hsrcI, hdstI, hdisjI, ?_, hAI⟩
    · rw [orStepRf_get_x5, hx5,
        show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
      have h1 : (BitVec.ofNat 64 (32 - i)).toNat = 32 - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (32 - (i + 1))).toNat = 32 - (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [orStepRf_get_x6, hx6,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      have h1 : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (8 * (i + 1))).toNat = 8 * (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [orStepRf_get_x7, hx7,
        show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide]
      have h1 : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (8 * (i + 1))).toNat = 8 * (i + 1) := by
        rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, orWin_drop, orWin_step srcBytes orig i holI hi]
  case bloomOrInto.loop.exhausted =>
    rintro rf ws A ⟨hx5, -, -, -, -, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx5, show (32 - 32 : Nat) = 0 from rfl]
    rfl
  case bloomOrInto.loop.body.step.mem =>
    rintro rf ws A hwslen
      ⟨i, hi, ⟨hx5, hx6, hx7, hile, hslI, holI, hsrcI, hdstI, hdisjI, hwin, hAI⟩, hcond⟩
    have hws256 : ws.length = 256 := hwslen
    have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
    have hi8 : (BitVec.ofNat 64 (8 * i)).toNat = 8 * i := by rw [BitVec.toNat_ofNat]; omega
    have hdst_addr : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = 8 * i := by
      rw [hx6, hse_0]; bv_omega
    have hx7' : (rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).get .x7
        + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 (8 * i) := by
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28), hx7, hse_0]; simp
    have hsrc_addr : (src + BitVec.ofNat 64 (8 * i) - src).toNat = 8 * i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, hi8]; omega
    have hmiss : ¬ inRw dst ws
        ((rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).get .x7
          + signExtend12 (0 : BitVec 12)) 8 := by
      rw [hx7']; unfold inRw; rw [hws256]
      have hsubd : (src + BitVec.ofNat 64 (8 * i) - dst).toNat
          = (src.toNat + 8 * i + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, hi8]; congr 1; omega
      rw [hsubd]; rcases hdisjI with hd | hd <;> omega
    simp only [show (bloomOrIntoFn src dst srcBytes orig).rw.base = dst from rfl,
      show (bloomOrIntoFn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl]
    rw [show orStepBlock = [.LD .x28 .x6 (0 : BitVec 12), .LD .x29 .x7 (0 : BitVec 12),
        .OR .x28 .x28 .x29, .SD .x6 .x28 (0 : BitVec 12),
        .ADDI .x6 .x6 (8 : BitVec 12), .ADDI .x7 .x7 (8 : BitVec 12),
        .ADDI .x5 .x5 (-1 : BitVec 12)] from rfl]
    refine ⟨?_, ?_⟩
    · -- LD dst: routes to the writable window, aligned, fits
      simp only [loadSem]
      rw [if_pos (show inRw dst ws (rf.get .x6 + signExtend12 (0 : BitVec 12)) 8 from by
        unfold inRw; rw [hdst_addr, hws256]; omega)]
      unfold Region.loadOk
      rw [hdst_addr, hws256]
      exact ⟨⟨i, rfl⟩, by omega⟩
    · rw [execInstrRF_ld_dword _ _ _ _ _ _ _ (8 * i)
          (packBytes ((ws.drop (8 * i)).take 8)) hdst_addr (by rw [hws256]; omega) rfl]
      refine ⟨?_, ?_⟩
      · -- LD src: misses the writable window, routes to the read-only region
        simp only [loadSem]
        rw [if_neg hmiss]
        unfold Region.loadOk
        rw [hx7']
        show 8 ∣ (src + BitVec.ofNat 64 (8 * i) - src).toNat
          ∧ (src + BitVec.ofNat 64 (8 * i) - src).toNat + 8 ≤ srcBytes.length
        rw [hsrc_addr, hslI]
        exact ⟨⟨i, rfl⟩, by omega⟩
      · rw [ld_dword_romiss _ _ _ _ _ _ _ (packBytes ((srcBytes.drop (8 * i)).take 8)) hmiss
          (by
            show Region.dwordAt ⟨src, srcBytes⟩
                ((rf.set .x28 (packBytes ((ws.drop (8 * i)).take 8))).get .x7
                  + signExtend12 (0 : BitVec 12)) = _
            rw [hx7']
            show packBytes ((srcBytes.drop ((src + BitVec.ofNat 64 (8 * i) - src).toNat)).take 8) = _
            rw [hsrc_addr])]
        -- [OR, SD, ADDI, ADDI, ADDI]
        refine ⟨trivial, ?_⟩
        dsimp only [execInstrRF, aluSem]
        refine ⟨⟨?_, ?_⟩, blockVCs_of_not_hasLoad _ _ _ _ _ (by decide)⟩
        · unfold inRw
          rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hdst_addr, hws256]
          show 8 * i + 8 ≤ 256
          omega
        · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29),
            RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hdst_addr]
          exact ⟨i, rfl⟩
  case bloomOrInto.post =>
    rintro rf ws A ⟨rf₀, ws₀, hlen₀,
      ⟨⟨i, hile, hx5, hx6, hx7, hi2, hslP, holP, hsrcP, hdstP, hdisjP, hwin, hAP⟩, hncond⟩,
      rfl, rfl⟩
    have hi32 : i = 32 := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx5] at hncond
      have hz : rf₀.get .x0 = 0 := rfl
      rw [hz] at hncond
      have : (BitVec.ofNat 64 (32 - i)).toNat = (0 : Word).toNat := by rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at this
      omega
    subst hi32
    refine ⟨?_, ?_, hAP⟩
    · simp only [epiBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide : Reg.x10 ≠ .x0)]
    · rw [hwin, orWin_full srcBytes orig holP]

/-! ## Flat linked-entry contract -/

def bloomOrIntoCr : CodeReq :=
  CodeReq.ofProg (GuestAddrs.bloom_or_into : Word) bloomOrInto_prog

/-- Exposed registers other than the two bloom pointers. -/
def bloomOrIntoScratch : List Reg :=
  [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
   .x12, .x13, .x14, .x15, .x16, .x17]

private theorem exposedRegs_split_bloom (vf : Reg → Word) :
    regAtomsOf vf exposedRegs =
      ((.x10 ↦ᵣ vf .x10) ** (.x11 ↦ᵣ vf .x11) **
        regAtomsOf vf bloomOrIntoScratch) := by
  show regAtomsOf vf
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31,
       .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] = _
  simp only [bloomOrIntoScratch, regAtomsOf_cons, regAtomsOf_nil]
  xperm

private theorem bloom_args_notin_scratch :
    ∀ r ∈ bloomOrIntoScratch, r ≠ (.x10 : Reg) ∧ r ≠ (.x11 : Reg) := by
  decide

theorem bloomOrIntoFlat_spec (ret src dst : Word)
    (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf)
    (hrww : RwRegion.wf ⟨dst, 256⟩)
    (hsrcLen : srcBytes.length = 256)
    (horigLen : orig.length = 256)
    (hsrcBound : src.toNat + 256 < 2 ^ 64)
    (hdstBound : dst.toNat + 256 < 2 ^ 64)
    (hdisj : src.toNat + 256 ≤ dst.toNat ∨ dst.toNat + 256 ≤ src.toNat)
    (hsz : 4 * ((bloomOrIntoFn src dst srcBytes orig).body.size + 1) ≤ 2 ^ 64)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin ((bloomOrIntoFn src dst srcBytes orig).body.steps + 1)
      (GuestAddrs.bloom_or_into : Word) ret bloomOrIntoCr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
        regOwns bloomOrIntoScratch ** bytesRegion dst orig **
        bytesRegion src srcBytes)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ 0) ** regOwn .x11 **
        regOwns bloomOrIntoScratch **
        bytesRegion dst ((List.range 256).map (orByte srcBytes orig)) **
        bytesRegion src srcBytes) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bloomOrIntoScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** (.x10 ↦ᵣ dst) ** (.x11 ↦ᵣ src) **
        bytesRegion dst orig ** bytesRegion src srcBytes)
      (fun vf => ?_))
  have hpre : (bloomOrIntoFn src dst srcBytes orig).pre
      (fun r => if r = .x10 then dst else if r = .x11 then src else vf r)
      orig empAssertion := by
    refine ⟨?_, ?_, rfl, horigLen, hsrcLen, hsrcBound, hdstBound, hdisj, rfl⟩
    · show RegFile.get _ .x10 = dst
      rw [RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]
      exact if_pos rfl
    · show RegFile.get _ .x11 = src
      rw [RegFile.get, if_neg (by decide : (Reg.x11 : Reg) ≠ .x0)]
      rw [if_neg (by decide : (Reg.x11 : Reg) ≠ .x10)]
      exact if_pos rfl
  have had := Fn.retSpecFlatAmbient
    (bloomOrIntoFn src dst srcBytes orig)
    (GuestAddrs.bloom_or_into : Word)
    (bloomOrIntoFn_spec src dst srcBytes orig hwf hrww
      (GuestAddrs.bloom_or_into : Word))
    hsz ret halign
    (fun r => if r = .x10 then dst else if r = .x11 then src else vf r)
    orig empAssertion pcFree_emp
      (by simpa [bloomOrIntoFn] using horigLen) hpre
    (Q := (.x10 ↦ᵣ 0) ** regOwn .x11 ** regOwns bloomOrIntoScratch **
      bytesRegion dst ((List.range 256).map (orByte srcBytes orig)))
    (fun _ _ _ hpost => hpost.2.2)
    (fun rf' ws' _hlen' hpost hp hh => by
      obtain ⟨hx10', hws', _hA⟩ := hpost
      rw [show ((bloomOrIntoFn src dst srcBytes orig).rw.base : Word) = dst from rfl,
        hws'] at hh
      simp only [sepConj_emp_right'] at hh
      rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
        exposedRegs_split_bloom,
        show rf' .x10 = 0 from by
          rw [← hx10', RegFile.get, if_neg (by decide : (Reg.x10 : Reg) ≠ .x0)]] at hh
      have hh2 := sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono
            (regIs_to_regOwn .x11 (rf' .x11))
            (regAtomsOf_to_regOwns (fun r => rf' r) bloomOrIntoScratch))) hp hh
      xperm_hyp hh2)
  rw [show (bloomOrIntoFn src dst srcBytes orig).programRet
      (GuestAddrs.bloom_or_into : Word) = bloomOrInto_prog from rfl] at had
  rw [show (bloomOrIntoFn src dst srcBytes orig).rw.base = dst from rfl,
    show (bloomOrIntoFn src dst srcBytes orig).region = (⟨src, srcBytes⟩ : Region) from rfl] at had
  rw [regFileIs_eq_regAtoms, regAtoms_eq_regAtomsOf _ _ (by decide),
    exposedRegs_split_bloom,
    show (if (Reg.x10 : Reg) = .x10 then dst else
        if (Reg.x10 : Reg) = .x11 then src else vf .x10) = dst from if_pos rfl,
    show (if (Reg.x11 : Reg) = .x10 then dst else
        if (Reg.x11 : Reg) = .x11 then src else vf .x11) = src from by
      rw [if_neg (by decide : ¬ ((Reg.x11 : Reg) = .x10))]
      exact if_pos rfl,
    regAtomsOf_congr
      (fun r => if r = .x10 then dst else if r = .x11 then src else vf r)
      vf bloomOrIntoScratch
      (fun r hr => by
        show (if r = .x10 then dst else if r = .x11 then src else vf r) = vf r
        rw [if_neg (fun (hc : r = .x10) =>
              (bloom_args_notin_scratch r hr).1 hc),
            if_neg (fun (hc : r = .x11) =>
              (bloom_args_notin_scratch r hr).2 hc)])] at had
  simp only [sepConj_emp_right'] at had
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) had

/-! ## Byte-identity to the emitted routine -/

-- The structured flatten is exactly `bloomOrInto_prog` minus the trailing
-- `ret`: prologue (3) ++ while (guard + 7-instr body + JAL back = 9) ++
-- epilogue (1) = 13 instrs; `++ [ret]` = the 14-instr emitted routine.
#guard (bloomOrBody 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0]
    = bloomOrInto_prog

-- Position independence: no PC-relative instructions leak an absolute address.
#guard (bloomOrBody 0 0 [] []).flatten 0
    = (bloomOrBody 0 0 [] []).flatten 0x80000000

#guard bloomOrInto_prog.length = 14

end BloomOrIntoSAsm

end EvmAsm.Codegen
