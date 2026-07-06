/-
  EvmAsm.Codegen.Programs.Secp256k1FieldLeavesSAsm

  Verified SAsm ports of the STRAIGHT-LINE secp256k1 field leaves
  (bead evm-asm-4ch8f.38.2.1, the wave-1 `.38a` stack):

  - `secfZero32` (`secfZero32_prog`, Secp256k1Field.lean): zero the 32-byte
    buffer at `a0` — four `SD x0` dword stores.  Modelled over a single
    WRITABLE region `⟨dst, 32⟩`; post pins `ws = replicate 32 0`.
  - `secfCopy32` (`secfCopy32_prog`): copy the 32 bytes at `a0` (read-only)
    into the buffer at `a1` (writable) — four interleaved `LD`/`SD` dword
    pairs.  Two regions: READ-ONLY `⟨src, srcBytes⟩` and WRITABLE
    `⟨dst, 32⟩`, disjoint (`hdisj`, like `SgMemcpySAsm`); post `ws = srcBytes`.

  Both bodies are straight-line (`.block`) — no loop combinator, no callees,
  no accelerator — so they are DSL-expressible and byte-identical to the
  emitted `_prog` NOW (unblocked, unlike the mul/pow stack which routes
  through the do-while BE<->LE converters, bead .11.7/.68).

  Byte-identity is kernel-pinned: `<body>.flatten 0 ++ [ret] = secf…_prog`.
  Spec-only module (no emitted-code change) — no EEST A/B required.

  (`secfGetBitLsb` is deferred: its post is a bit-extraction against the
  BE-decoded value and wants the `.38.1` `beBytesToNat`/`testBit` vocabulary.)
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.MultiRw
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.Secp256k1Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace Secp256k1FieldLeavesSAsm

-- ============================================================================
-- secfZero32 : zero the 32-byte buffer at a0
-- ============================================================================

def secfZero32Body : Stmt :=
  .block "z"
    [.SD .x10 .x0 (0 : BitVec 12), .SD .x10 .x0 (8 : BitVec 12),
     .SD .x10 .x0 (16 : BitVec 12), .SD .x10 .x0 (24 : BitVec 12)]

def secfZero32Fn (dst : Word) (orig : List (BitVec 8)) : Fn where
  name := "secfZero32"
  rw := ⟨dst, 32⟩
  pre := fun rf ws _ => rf.get .x10 = dst ∧ ws = orig ∧ orig.length = 32
  post := fun _ ws _ => ws = List.replicate 32 (0 : BitVec 8)
  body := secfZero32Body

def secfZero32_verified : Program := secfZero32Body.flatten 0

#guard (secfZero32_verified : List Instr).length = 4
#guard secfZero32Body.flatten 0 = secfZero32Body.flatten 0x80000000
-- Byte-identity to the emitted routine: the four dword stores plus the
-- calling-convention `ret` epilogue reproduce `secfZero32_prog` exactly.
#guard secfZero32Body.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
  = secfZero32_prog

/-- `signExtend12` of the four dword offsets, as concrete words. -/
private theorem se12_z0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
private theorem se12_z8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
private theorem se12_z16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
private theorem se12_z24 : signExtend12 (24 : BitVec 12) = (24 : Word) := by decide

/-- `l[i] = getByteAt l i` for an in-range index. -/
private theorem getElem_eq_getByteAt (l : List (BitVec 8)) (i : Nat)
    (h : i < l.length) : l[i] = getByteAt l i := by
  unfold getByteAt; rw [dif_pos h]

/-- Every byte of the zero dword is zero. -/
private theorem getByteAt_dword0 (j : Nat) (hj : j < 8) :
    getByteAt (dwordBytes (0 : Word)) j = 0 := by
  have hd : dwordBytes (0 : Word) = List.replicate 8 (0 : BitVec 8) := by decide
  unfold getByteAt
  rw [hd, dif_pos (by rw [List.length_replicate]; exact hj), List.getElem_replicate]

/-- The full 32-byte cover: writing the zero dword at offsets 0/8/16/24 of any
    32-byte buffer yields the all-zero buffer. -/
private theorem zeroFold (l : List (BitVec 8)) (hl : l.length = 32) :
    setBytes (setBytes (setBytes (setBytes l 0 (dwordBytes 0)) 8 (dwordBytes 0))
        16 (dwordBytes 0)) 24 (dwordBytes 0)
      = List.replicate 32 (0 : BitVec 8) := by
  apply List.ext_getElem
  · simp only [length_setBytes, hl, List.length_replicate]
  · intro i h1 _
    have hi : i < 32 := by simp only [length_setBytes, hl] at h1; exact h1
    have g24 : (24 : Nat) + (dwordBytes (0 : Word)).length ≤
        (setBytes (setBytes (setBytes l 0 (dwordBytes 0)) 8 (dwordBytes 0))
          16 (dwordBytes 0)).length := by simp only [length_setBytes, length_dwordBytes, hl]; omega
    have g16 : (16 : Nat) + (dwordBytes (0 : Word)).length ≤
        (setBytes (setBytes l 0 (dwordBytes 0)) 8 (dwordBytes 0)).length := by
      simp only [length_setBytes, length_dwordBytes, hl]; omega
    have g8 : (8 : Nat) + (dwordBytes (0 : Word)).length ≤
        (setBytes l 0 (dwordBytes 0)).length := by
      simp only [length_setBytes, length_dwordBytes, hl]; omega
    have g0 : (0 : Nat) + (dwordBytes (0 : Word)).length ≤ l.length := by
      simp only [length_dwordBytes, hl]; omega
    rw [getElem_eq_getByteAt _ _ h1, List.getElem_replicate,
      getByteAt_setBytes _ _ _ _ g24, getByteAt_setBytes _ _ _ _ g16,
      getByteAt_setBytes _ _ _ _ g8, getByteAt_setBytes _ _ _ _ g0]
    simp only [length_dwordBytes]
    by_cases c24 : 24 ≤ i ∧ i < 24 + 8
    · rw [if_pos c24, getByteAt_dword0 _ (by omega)]
    · rw [if_neg c24]
      by_cases c16 : 16 ≤ i ∧ i < 16 + 8
      · rw [if_pos c16, getByteAt_dword0 _ (by omega)]
      · rw [if_neg c16]
        by_cases c8 : 8 ≤ i ∧ i < 8 + 8
        · rw [if_pos c8, getByteAt_dword0 _ (by omega)]
        · rw [if_neg c8, if_pos (by omega), getByteAt_dword0 _ (by omega)]

/-- Engine (own heartbeat budget): the four zero-dword stores blank the whole
    32-byte writable window, leaving the registers untouched. -/
private theorem zero_engine (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (hx10 : rf.get .x10 = dst) (hws : ws.length = 32) :
    execBlock reg dst rf ws
        [Instr.SD Reg.x10 Reg.x0 0, Instr.SD Reg.x10 Reg.x0 8,
         Instr.SD Reg.x10 Reg.x0 16, Instr.SD Reg.x10 Reg.x0 24]
      = (rf, List.replicate 32 (0 : BitVec 8)) := by
  have hx0 : rf.get .x0 = (0 : Word) := RegFile.get_x0 rf
  simp only [execBlock, execInstrRF, storeSem, loadSem, aluSem, hx10, hx0,
    se12_z0, se12_z8, se12_z16, se12_z24]
  rw [show (dst + 0 - dst).toNat = 0 from by bv_omega,
    show (dst + 8 - dst).toNat = 8 from by bv_omega,
    show (dst + 16 - dst).toNat = 16 from by bv_omega,
    show (dst + 24 - dst).toNat = 24 from by bv_omega, zeroFold ws hws]

/-- Address side conditions of the zero block (own heartbeat budget). -/
private theorem zero_blockVCs (reg : Region) (dst : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (hx10 : rf.get .x10 = dst) (hws : ws.length = 32) :
    blockVCs reg dst rf ws
      [Instr.SD Reg.x10 Reg.x0 0, Instr.SD Reg.x10 Reg.x0 8,
       Instr.SD Reg.x10 Reg.x0 16, Instr.SD Reg.x10 Reg.x0 24] := by
  simp only [blockVCs, inRw, execInstrRF, storeSem, loadSem, aluSem, length_setBytes,
    hx10, hws, se12_z0, se12_z8, se12_z16, se12_z24]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> constructor <;> bv_omega

theorem secfZero32Fn_spec (dst : Word) (orig : List (BitVec 8))
    (hwf : RwRegion.wf ⟨dst, 32⟩) (base : Word) :
    (secfZero32Fn dst orig).Spec base := by
  vcgen
  case region => exact ⟨Region.empty_wf, hwf⟩
  case secfZero32.z.mem =>
    rintro rf ws A hlen ⟨hx10, -, -⟩
    exact zero_blockVCs _ dst rf ws hx10 hlen
  case secfZero32.post =>
    rintro rf ws A ⟨rf₀, ws₀, hlen, ⟨hx10, hwseq, hlenorig⟩, hrfeq, hwseq2⟩
    subst ws₀
    rw [hwseq2]
    exact congrArg Prod.snd (zero_engine _ dst rf₀ orig hx10 hlenorig)

-- ============================================================================
-- secfCopy32 : copy the 32 bytes at a0 (ro) into a1 (rw)
-- ============================================================================

def secfCopy32Body : Stmt :=
  .block "c"
    [.LD .x5 .x10 (0 : BitVec 12), .SD .x11 .x5 (0 : BitVec 12),
     .LD .x5 .x10 (8 : BitVec 12), .SD .x11 .x5 (8 : BitVec 12),
     .LD .x5 .x10 (16 : BitVec 12), .SD .x11 .x5 (16 : BitVec 12),
     .LD .x5 .x10 (24 : BitVec 12), .SD .x11 .x5 (24 : BitVec 12)]

def secfCopy32Fn (src dst : Word) (srcBytes orig : List (BitVec 8)) : Fn where
  name := "secfCopy32"
  region := ⟨src, srcBytes⟩
  rw := ⟨dst, 32⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = dst ∧ ws = orig ∧ orig.length = 32 ∧
    srcBytes.length = 32 ∧
    src.toNat + 32 < 2 ^ 64 ∧ dst.toNat + 32 < 2 ^ 64 ∧
    (src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat)
  post := fun _ ws _ => ws = srcBytes
  body := secfCopy32Body

def secfCopy32_verified : Program := secfCopy32Body.flatten 0

#guard (secfCopy32_verified : List Instr).length = 8
#guard secfCopy32Body.flatten 0 = secfCopy32Body.flatten 0x80000000
-- Byte-identity to the emitted routine.
#guard secfCopy32Body.flatten 0 ++ [Instr.JALR .x0 .x1 (0 : BitVec 12)]
  = secfCopy32_prog

/-- Byte `j` of the `k`-offset 8-byte source chunk is byte `k+j` of the source. -/
private theorem getByteAt_take8_drop (srcBytes : List (BitVec 8)) (k j : Nat)
    (hkj : k + j < srcBytes.length) (hj : j < 8) :
    getByteAt ((srcBytes.drop k).take 8) j = getByteAt srcBytes (k + j) := by
  have hlen : ((srcBytes.drop k).take 8).length = min 8 (srcBytes.length - k) := by
    rw [List.length_take, List.length_drop]
  unfold getByteAt
  rw [dif_pos (by rw [hlen]; omega), dif_pos (by omega),
    List.getElem_take, List.getElem_drop]

/-- The four dword loads reconstruct the source buffer. -/
private theorem copyFold (orig srcBytes : List (BitVec 8))
    (ho : orig.length = 32) (hs : srcBytes.length = 32) :
    setBytes (setBytes (setBytes
        (setBytes orig 0 (dwordBytes (packBytes ((srcBytes.drop 0).take 8))))
        8 (dwordBytes (packBytes ((srcBytes.drop 8).take 8))))
        16 (dwordBytes (packBytes ((srcBytes.drop 16).take 8))))
        24 (dwordBytes (packBytes ((srcBytes.drop 24).take 8)))
      = srcBytes := by
  rw [dwordBytes_packBytes _ (by rw [List.length_take, List.length_drop, hs]; omega),
    dwordBytes_packBytes _ (by rw [List.length_take, List.length_drop, hs]; omega),
    dwordBytes_packBytes _ (by rw [List.length_take, List.length_drop, hs]; omega),
    dwordBytes_packBytes _ (by rw [List.length_take, List.length_drop, hs]; omega)]
  apply List.ext_getElem
  · simp only [length_setBytes, ho, hs]
  · intro i h1 _
    have hi : i < 32 := by simp only [length_setBytes, ho] at h1; exact h1
    have g24 : (24 : Nat) + ((srcBytes.drop 24).take 8).length ≤
        (setBytes (setBytes (setBytes orig 0 ((srcBytes.drop 0).take 8))
          8 ((srcBytes.drop 8).take 8)) 16 ((srcBytes.drop 16).take 8)).length := by
      simp only [length_setBytes, List.length_take, List.length_drop, ho, hs]; omega
    have g16 : (16 : Nat) + ((srcBytes.drop 16).take 8).length ≤
        (setBytes (setBytes orig 0 ((srcBytes.drop 0).take 8))
          8 ((srcBytes.drop 8).take 8)).length := by
      simp only [length_setBytes, List.length_take, List.length_drop, ho, hs]; omega
    have g8 : (8 : Nat) + ((srcBytes.drop 8).take 8).length ≤
        (setBytes orig 0 ((srcBytes.drop 0).take 8)).length := by
      simp only [length_setBytes, List.length_take, List.length_drop, ho, hs]; omega
    have g0 : (0 : Nat) + ((srcBytes.drop 0).take 8).length ≤ orig.length := by
      simp only [List.length_take, List.length_drop, ho, hs]; omega
    rw [getElem_eq_getByteAt _ _ h1, getByteAt_setBytes _ _ _ _ g24,
      getByteAt_setBytes _ _ _ _ g16, getByteAt_setBytes _ _ _ _ g8,
      getByteAt_setBytes _ _ _ _ g0]
    have hchunk : ∀ k : Nat, k + 8 ≤ 32 → ((srcBytes.drop k).take 8).length = 8 := by
      intro k hk; rw [List.length_take, List.length_drop, hs]; omega
    simp only [hchunk 0 (by omega), hchunk 8 (by omega), hchunk 16 (by omega),
      hchunk 24 (by omega)]
    rw [getElem_eq_getByteAt srcBytes i (by rw [hs]; exact hi)]
    by_cases c24 : 24 ≤ i ∧ i < 24 + 8
    · rw [if_pos c24, getByteAt_take8_drop _ _ _ (by rw [hs]; omega) (by omega)]
      congr 1; omega
    · rw [if_neg c24]
      by_cases c16 : 16 ≤ i ∧ i < 16 + 8
      · rw [if_pos c16, getByteAt_take8_drop _ _ _ (by rw [hs]; omega) (by omega)]
        congr 1; omega
      · rw [if_neg c16]
        by_cases c8 : 8 ≤ i ∧ i < 8 + 8
        · rw [if_pos c8, getByteAt_take8_drop _ _ _ (by rw [hs]; omega) (by omega)]
          congr 1; omega
        · rw [if_neg c8, if_pos (by omega),
            getByteAt_take8_drop _ _ _ (by rw [hs]; omega) (by omega)]
          congr 1; omega

/-- A load at `src + k` misses the writable window `⟨dst, 32⟩` (disjointness). -/
private theorem copy_load_miss (src dst : Word) (w : List (BitVec 8)) (k : Nat)
    (hwl : w.length = 32) (hk : k ≤ 24)
    (hnw_s : src.toNat + 32 < 2 ^ 64) (hnw_d : dst.toNat + 32 < 2 ^ 64)
    (hdisj : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat) :
    ¬ inRw dst w (src + BitVec.ofNat 64 k) 8 := by
  unfold inRw
  rw [hwl]
  rcases hdisj with h | h <;> bv_omega

/-- An `LD` that misses the writable window reads the read-only region,
    fully resolved (address + value) for one-`rw` dword chaining.  Local
    mirror of `MultiRw`'s private lemma (kept in-module per the port fence). -/
private theorem execInstrRF_ld_romiss (ro : Region) (rwBase : Word)
    (rf : RegFile) (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (v : Word)
    (hmiss : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 8)
    (hv : ro.dwordAt (rf.get rs1 + signExtend12 ofs) = v) :
    execInstrRF ro rwBase rf ws (.LD rd rs1 ofs) = (rf.set rd v, ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg hmiss, hv]

private theorem copy_engine (src dst : Word) (rf : RegFile) (ws srcBytes : List (BitVec 8))
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst)
    (hws : ws.length = 32) (hs : srcBytes.length = 32)
    (hnw_s : src.toNat + 32 < 2 ^ 64) (hnw_d : dst.toNat + 32 < 2 ^ 64)
    (hdisj : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat) :
    (execBlock ⟨src, srcBytes⟩ dst rf ws
      [Instr.LD Reg.x5 Reg.x10 0, Instr.SD Reg.x11 Reg.x5 0,
       Instr.LD Reg.x5 Reg.x10 8, Instr.SD Reg.x11 Reg.x5 8,
       Instr.LD Reg.x5 Reg.x10 16, Instr.SD Reg.x11 Reg.x5 16,
       Instr.LD Reg.x5 Reg.x10 24, Instr.SD Reg.x11 Reg.x5 24]).2 = srcBytes := by
  -- abbreviations for the loaded dwords (one per source offset)
  set v0 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 0) with hv0
  set v8 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 8) with hv8
  set v16 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 16) with hv16
  set v24 := Region.dwordAt ⟨src, srcBytes⟩ (src + signExtend12 24) with hv24
  have hxne : (Reg.x10 ≠ .x5) ∧ (Reg.x11 ≠ .x5) := ⟨by decide, by decide⟩
  -- load/store at offset 0
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst rf ws .x5 .x10 0 v0
    (by rw [hx10]; exact copy_load_miss src dst ws 0 hws (by omega) hnw_s hnw_d hdisj)
    (by rw [hv0, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ ws .x11 .x5 0 0
    (by rw [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_z0]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  -- load/store at offset 8
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 8 v8
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 8 (by simp [length_setBytes, hws]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv8, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 8 8
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_z8]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  -- load/store at offset 16
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 16 v16
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 16 (by simp [length_setBytes, hws]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv16, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 16 16
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_z16]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide)]
  -- load/store at offset 24
  rw [execBlock_cons, execInstrRF_ld_romiss ⟨src, srcBytes⟩ dst _ _ .x5 .x10 24 v24
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.1, hx10]
        exact copy_load_miss src dst _ 24 (by simp [length_setBytes, hws]) (by omega)
          hnw_s hnw_d hdisj)
    (by simp only [hv24, RegFile.get_set_ne _ _ _ _ hxne.1, hx10])]
  dsimp only
  rw [execBlock_cons, execInstrRF_sd_dword ⟨src, srcBytes⟩ dst _ _ .x11 .x5 24 24
    (by simp only [RegFile.get_set_ne _ _ _ _ hxne.2, hx11, se12_z24]; bv_omega)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), execBlock_nil]
  -- reduce each loaded dword to the corresponding source chunk, then reconstruct
  dsimp only
  rw [hv0, hv8, hv16, hv24]
  simp only [Region.dwordAt, se12_z0, se12_z8, se12_z16, se12_z24]
  rw [show (src + 0 - src).toNat = 0 from by bv_omega,
    show (src + 8 - src).toNat = 8 from by bv_omega,
    show (src + 16 - src).toNat = 16 from by bv_omega,
    show (src + 24 - src).toNat = 24 from by bv_omega]
  exact copyFold ws srcBytes hws hs

/-- Address side conditions of the copy block (own heartbeat budget): each
    `LD` routes to the read-only source region (missing the disjoint `rw`
    window, offset aligned + in range), each `SD` into the `rw` window at an
    aligned in-range offset.  Registers `x10`/`x11` (the two pointers) are
    never written, so all addresses stay `src+k` / `dst+k`. -/
private theorem copy_blockVCs (src dst : Word) (rf : RegFile) (ws srcBytes : List (BitVec 8))
    (hx10 : rf.get .x10 = src) (hx11 : rf.get .x11 = dst)
    (hws : ws.length = 32) (hs : srcBytes.length = 32)
    (hnw_s : src.toNat + 32 < 2 ^ 64) (hnw_d : dst.toNat + 32 < 2 ^ 64)
    (hdisj : src.toNat + 32 ≤ dst.toNat ∨ dst.toNat + 32 ≤ src.toNat) :
    blockVCs ⟨src, srcBytes⟩ dst rf ws
      [Instr.LD Reg.x5 Reg.x10 0, Instr.SD Reg.x11 Reg.x5 0,
       Instr.LD Reg.x5 Reg.x10 8, Instr.SD Reg.x11 Reg.x5 8,
       Instr.LD Reg.x5 Reg.x10 16, Instr.SD Reg.x11 Reg.x5 16,
       Instr.LD Reg.x5 Reg.x10 24, Instr.SD Reg.x11 Reg.x5 24] := by
  have hxne1 : Reg.x10 ≠ Reg.x5 := by decide
  have hxne2 : Reg.x11 ≠ Reg.x5 := by decide
  -- The read-only load-OK obligation at source offset `k` (k ∈ {0,8,16,24}).
  -- Phrased over `signExtend12 ofs` (not `BitVec.ofNat 64 k`) so the head VC
  -- discharge unifies SYNTACTICALLY against `blockVCs`'s `signExtend12` address
  -- — no per-step `signExtend12`-literal reduction, which would exhaust the
  -- `whnf` budget across the eight conjuncts.  `hofs` bridges the two forms.
  have hload : ∀ (r : RegFile) (w : List (BitVec 8)) (ofs : BitVec 12) (k : Nat),
      r.get .x10 = src → w.length = 32 → signExtend12 ofs = BitVec.ofNat 64 k →
      k ≤ 24 → 8 ∣ k →
      (if inRw dst w (r.get .x10 + signExtend12 ofs) 8
        then (Region.mk dst w).loadOk (r.get .x10 + signExtend12 ofs) 8
        else (Region.mk src srcBytes).loadOk (r.get .x10 + signExtend12 ofs) 8) := by
    intro r w ofs k hr hwl hofs hk hdvd
    rw [hofs, hr, if_neg (copy_load_miss src dst w k hwl hk hnw_s hnw_d hdisj)]
    refine ⟨?_, ?_⟩
    · show (8 : Nat) ∣ ((src + BitVec.ofNat 64 k) - src).toNat
      rw [show ((src + BitVec.ofNat 64 k) - src).toNat = k from by bv_omega]; exact hdvd
    · show ((src + BitVec.ofNat 64 k) - src).toNat + 8 ≤ srcBytes.length
      rw [show ((src + BitVec.ofNat 64 k) - src).toNat = k from by bv_omega, hs]; omega
  -- The store obligation at destination offset `k`.
  have hstore : ∀ (r : RegFile) (w : List (BitVec 8)) (ofs : BitVec 12) (k : Nat),
      r.get .x11 = dst → w.length = 32 → signExtend12 ofs = BitVec.ofNat 64 k →
      k ≤ 24 → 8 ∣ k →
      inRw dst w (r.get .x11 + signExtend12 ofs) 8
        ∧ (8 : Nat) ∣ ((r.get .x11 + signExtend12 ofs) - dst).toNat := by
    intro r w ofs k hr hwl hofs hk hdvd
    rw [hofs, hr]
    refine ⟨?_, ?_⟩
    · show ((dst + BitVec.ofNat 64 k) - dst).toNat + 8 ≤ w.length
      rw [show ((dst + BitVec.ofNat 64 k) - dst).toNat = k from by bv_omega, hwl]; omega
    · rw [show ((dst + BitVec.ofNat 64 k) - dst).toNat = k from by bv_omega]; exact hdvd
  -- A load at source offset `k` misses the writable window, phrased over the
  -- goal's `rf.get x10 + signExtend12 ofs` address so `if_neg` fires directly.
  have hmiss : ∀ (w : List (BitVec 8)) (ofs : BitVec 12) (k : Nat), w.length = 32 →
      signExtend12 ofs = BitVec.ofNat 64 k → k ≤ 24 →
      ¬ inRw dst w (rf.get .x10 + signExtend12 ofs) 8 := by
    intro w ofs k hwl hofs hk
    rw [hofs, hx10]; exact copy_load_miss src dst w k hwl hk hnw_s hnw_d hdisj
  -- One shared pass: unfold `blockVCs` and resolve every threaded state through
  -- the engine-step projections — a store never touches the register file
  -- (`execInstrRF_sd_fst`), a load never touches the window
  -- (`execInstrRF_ld_snd`), a store splices the window (`execInstrRF_sd_snd`),
  -- and neither load touches the two pointers (`execInstrRF_ld_get_ne`) — so
  -- every threaded read is `rf.get x10` / `rf.get x11`.  Then route each load
  -- to the read-only region with `if_neg` (discarding the writable `then`
  -- branch, whose window is large), and discharge the resulting arithmetic.
  simp only [blockVCs, loadSem, storeSem, execInstrRF_ld_snd, execInstrRF_sd_fst,
    execInstrRF_sd_snd, execInstrRF_ld_get_ne (h := hxne1),
    execInstrRF_ld_get_ne (h := hxne2)]
  rw [if_neg (hmiss _ 0 0 (by simp only [hws]) se12_z0 (by decide)),
    if_neg (hmiss _ 8 8 (by simp only [length_setBytes, hws]) se12_z8 (by decide)),
    if_neg (hmiss _ 16 16 (by simp only [length_setBytes, hws]) se12_z16 (by decide)),
    if_neg (hmiss _ 24 24 (by simp only [length_setBytes, hws]) se12_z24 (by decide))]
  simp only [Region.loadOk, inRw, hx10, hx11, se12_z0, se12_z8, se12_z16, se12_z24,
    length_setBytes, hws, hs]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, trivial⟩ <;> bv_omega

theorem secfCopy32Fn_spec (src dst : Word) (srcBytes orig : List (BitVec 8))
    (hwf : (Region.mk src srcBytes).wf) (hrww : RwRegion.wf ⟨dst, 32⟩)
    (base : Word) :
    (secfCopy32Fn src dst srcBytes orig).Spec base := by
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case secfCopy32.c.mem =>
    rintro rf ws A hlen ⟨hx10, hx11, -, -, hs, hnws, hnwd, hdisj⟩
    exact copy_blockVCs src dst rf ws srcBytes hx10 hx11 hlen hs hnws hnwd hdisj
  case secfCopy32.post =>
    rintro rf ws A ⟨rf₀, ws₀, hlen,
      ⟨hx10, hx11, hwseq, hlenorig, hs, hnws, hnwd, hdisj⟩, hrfeq, hwseq2⟩
    subst ws₀
    rw [hwseq2]
    exact copy_engine src dst rf₀ orig srcBytes hx10 hx11 hlenorig hs hnws hnwd hdisj

end Secp256k1FieldLeavesSAsm

end EvmAsm.Codegen
