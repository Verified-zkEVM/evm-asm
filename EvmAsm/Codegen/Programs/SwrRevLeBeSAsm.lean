/-
  EvmAsm.Codegen.Programs.SwrRevLeBeSAsm

  Verified SAsm port of `swr_rev_le_be` (bead evm-asm-4ch8f.12.4): reverse the
  first `len` bytes of the source buffer `a0` into the destination `a2`.

  Source (`swrRevLeBe_prog` in SszWithdrawal.lean): a0=src, a1=len, a2=dst.
  `x5 := src+len; x6 := dst; x7 := len; while x7≠0 { x5--; b := src[x5];
  dst[x6] := b; x6++; x7-- }`.  Net: for j<len, dst[j] = src[len-1-j], i.e.
  dst = (src[0..len)).reverse.

  Two regions: a READ-ONLY region ⟨src, bs⟩ (the source bytes, read via LBU)
  and a WRITABLE region ⟨dst, len⟩ (written via SB).  These are combined with
  the separating `**` in `asrtM`, so they are heap-disjoint; but the block
  engine's `inRw` routing test is *arithmetic*, so to route each `LBU` to the
  read-only region (reading the true src byte, not a dst byte) the precondition
  must state src/dst disjointness explicitly (`hdisj`).  A caller with
  overlapping src/dst cannot satisfy the (unweakened) contract — matching the
  routine's real contract (reverse-copy into a *separate* buffer).

  Byte-identity: the loop counter is `x7` and the `while` guard sits right
  after the 3-instr init, so the structured back-edge targets the guard exactly
  as the emitted `JAL -24` does — full `flatten ++ [ret] = swrRevLeBe_prog` is
  pinned.  Spec-only module (no emitted-code change) — no EEST A/B.

  Generic in (src, dst, len, bs) so bead .12.5 `bhr_rev_le_be` (byte-identical
  `bhrRevLeBe_prog`) can reuse this core.
-/

import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Codegen.Programs.SszWithdrawal

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.SAsm.Stmt

namespace SwrRevLeBeSAsm

/-- The `k`-th output byte: source byte at index `len-1-k`. -/
def revByte (bs : List (BitVec 8)) (len k : Nat) : BitVec 8 :=
  bs.getD (len - 1 - k) 0

/-- Loop window: first `i` output bytes are the reversed prefix, the rest is
    the untouched tail of the original dst buffer. -/
def revWin (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8)) (i : Nat) :
    List (BitVec 8) :=
  (List.range i).map (revByte bs len) ++ orig.drop i

#guard revWin [10,20,30] 3 [0,0,0] 0 = [0,0,0]
#guard (List.range 3).map (revByte [10,20,30] 3) = [30,20,10]

theorem revWin_zero (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8)) :
    revWin bs len orig 0 = orig := by
  simp [revWin]

theorem length_revWin (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8))
    (i : Nat) (h : orig.length = len) (hi : i ≤ len) :
    (revWin bs len orig i).length = len := by
  simp only [revWin, List.length_append, List.length_map, List.length_range,
    List.length_drop, h]
  omega

theorem revWin_step (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8))
    (i : Nat) (h : orig.length = len) (hi : i < len) :
    setBytes (revWin bs len orig i) i [revByte bs len i]
      = revWin bs len orig (i + 1) := by
  rw [setBytes_singleton]
  have hpre : ((List.range i).map (revByte bs len)).length = i := by simp
  have hdrop : orig.drop i = orig[i] :: orig.drop (i + 1) :=
    List.drop_eq_getElem_cons (by omega)
  simp only [revWin, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]
  rw [hdrop]
  simp only [hpre, List.set_append_right, Nat.le_refl, Nat.sub_self,
    List.set_cons_zero]

theorem revWin_len_eq (bs : List (BitVec 8)) (len : Nat) (orig : List (BitVec 8))
    (h : orig.length = len) (hlen : len ≤ bs.length) :
    revWin bs len orig len = (bs.take len).reverse := by
  have hnil : orig.drop len = [] := by simp [h]
  simp only [revWin, hnil, List.append_nil]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_reverse,
      List.length_take]; omega
  · intro j hj1 hj2
    simp only [List.length_map, List.length_range] at hj1
    have hlt : (bs.take len).length = len := by rw [List.length_take]; omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, hlt, revByte,
      List.getElem_take, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show len - 1 - j < bs.length by omega), Option.getD_some]

def swrRevLeBeInitBlock : List Instr :=
  [.ADD .x5 .x10 .x11, .MV .x6 .x12, .MV .x7 .x11]

def swrRevLeBeStepBlock : List Instr :=
  [.ADDI .x5 .x5 (-1 : BitVec 12),
   .LBU .x28 .x5 0,
   .SB .x6 .x28 0,
   .ADDI .x6 .x6 1,
   .ADDI .x7 .x7 (-1 : BitVec 12)]

def swrRevLeBeInv (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x5 = src + BitVec.ofNat 64 (len - i) ∧
    rf.get .x6 = dst + BitVec.ofNat 64 i ∧
    rf.get .x7 = BitVec.ofNat 64 (len - i) ∧
    i ≤ len ∧ len ≤ bs.length ∧ orig.length = len ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat) ∧
    ws = revWin bs len orig i

def swrRevLeBeBody (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Stmt :=
  .block "init" swrRevLeBeInitBlock ;;;
  .«while» "loop" (.bne .x7 .x0) len (swrRevLeBeInv src dst len bs orig)
    (.block "step" swrRevLeBeStepBlock)

def swrRevLeBeFn (src dst : Word) (len : Nat) (bs orig : List (BitVec 8)) : Fn where
  name := "swrRevLeBe"
  region := ⟨src, bs⟩
  rw := ⟨dst, len⟩
  pre := fun rf ws _ =>
    rf.get .x10 = src ∧ rf.get .x11 = BitVec.ofNat 64 len ∧ rf.get .x12 = dst ∧
    ws = orig ∧ orig.length = len ∧ len ≤ bs.length ∧
    src.toNat + len < 2 ^ 64 ∧ dst.toNat + len < 2 ^ 64 ∧
    (src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
  post := fun _ ws _ => ws = (bs.take len).reverse
  body := swrRevLeBeBody src dst len bs orig

def swrRevLeBe_verified : Program :=
  (swrRevLeBeBody 0 0 0 [] []).flatten 0

#guard (swrRevLeBe_verified : List Instr).length = 10
#guard (swrRevLeBeBody 0 0 0 [] []).flatten 0 = (swrRevLeBeBody 0 0 0 [] []).flatten 0x80000000
#guard (swrRevLeBeBody 0 0 0 [] []).flatten 0 ++ [Instr.JALR .x0 .x1 0] = swrRevLeBe_prog

/-- An `LBU` that misses the writable window reads the read-only region. -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

/-- Register file after one loop body (given the loaded byte `b`). -/
def swrStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))
  let r2 := r1.set .x28 (b.zeroExtend 64)
  let r3 := r2.set .x6 (r2.get .x6 + signExtend12 (1 : BitVec 12))
  r3.set .x7 (r3.get .x7 + signExtend12 (-1 : BitVec 12))

theorem swrStepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (swrStepRf rf b).get .x5 = rf.get .x5 + signExtend12 (-1 : BitVec 12) := by
  unfold swrStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28),
    RegFile.get_set_self _ _ _ (by decide : Reg.x5 ≠ .x0)]

theorem swrStepRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (swrStepRf rf b).get .x6 = rf.get .x6 + signExtend12 (1 : BitVec 12) := by
  unfold swrStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_self _ _ _ (by decide : Reg.x6 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5)]

theorem swrStepRf_get_x7 (rf : RegFile) (b : BitVec 8) :
    (swrStepRf rf b).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold swrStepRf
  rw [RegFile.get_set_self _ _ _ (by decide : Reg.x7 ≠ .x0),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5)]

/-- Engine (own heartbeat budget): one loop body decrements the src cursor,
    loads `src[len-1-i]`, stores it at `dst[i]`, and advances the cursors. -/
theorem swr_step_engine (src dst : Word) (len i : Nat) (bs : List (BitVec 8))
    (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = src + BitVec.ofNat 64 (len - i))
    (hx6 : rf.get .x6 = dst + BitVec.ofNat 64 i)
    (hi : i < len)
    (hsrc : src.toNat + len < 2 ^ 64) (hdst : dst.toNat + len < 2 ^ 64)
    (hdisj : src.toNat + len ≤ dst.toNat ∨ dst.toNat + len ≤ src.toNat)
    (hws : ws.length = len) :
    execBlock ⟨src, bs⟩ dst rf ws swrRevLeBeStepBlock
      = (swrStepRf rf (revByte bs len i), setBytes ws i [revByte bs len i]) := by
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have hile : len - 1 - i < 2 ^ 64 := by omega
  -- decremented src cursor
  have h2 : (BitVec.ofNat 64 (len - 1 - i)).toNat = len - 1 - i := by
    rw [BitVec.toNat_ofNat]; omega
  have hx5dec : (rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))).get .x5
      = src + BitVec.ofNat 64 (len - 1 - i) := by
    rw [RegFile.get_set_self _ _ _ (by decide), hx5, hse_m1]
    have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
    bv_omega
  have hsub : (src + BitVec.ofNat 64 (len - 1 - i) - src).toNat = len - 1 - i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
    omega
  have hloadaddr : (rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))).get .x5
      + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 (len - 1 - i) := by
    rw [hx5dec, hse_0]; simp
  -- the load address is disjoint from the writable window
  have hnr : ¬ inRw dst ws
      ((rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))).get .x5
        + signExtend12 (0 : BitVec 12)) 1 := by
    rw [hloadaddr]
    unfold inRw
    rw [hws]
    have hsubd : (src + BitVec.ofNat 64 (len - 1 - i) - dst).toNat
        = (src.toNat + (len - 1 - i) + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
      congr 1; omega
    rw [hsubd]
    rcases hdisj with hd | hd <;> omega
  -- the loaded byte equals the reversed source byte
  have hval : (Region.byteAt ⟨src, bs⟩
      ((rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))).get .x5
        + signExtend12 (0 : BitVec 12))) = revByte bs len i := by
    rw [hloadaddr]
    show bs.getD ((src + BitVec.ofNat 64 (len - 1 - i) - src).toNat) 0 = revByte bs len i
    rw [hsub]; rfl
  -- store address index
  have hstore : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
    rw [hx6, hse_0]
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    bv_omega
  rw [show swrRevLeBeStepBlock =
      [.ADDI .x5 .x5 (-1 : BitVec 12), .LBU .x28 .x5 0, .SB .x6 .x28 0,
       .ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
  dsimp only
  rw [hval]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i
    (by rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5)]; exact hstore)]
  dsimp only
  rw [RegFile.get_set_self _ _ _ (by decide), setBytes_singleton,
    truncate_zeroExtend_byte]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold swrStepRf
  simp only [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5)]
  rw [setBytes_singleton]

theorem swrRevLeBeFn_spec (src dst : Word) (len : Nat) (bs orig : List (BitVec 8))
    (hwf : (Region.mk src bs).wf) (hrww : RwRegion.wf ⟨dst, len⟩) (base : Word) :
    (swrRevLeBeFn src dst len bs orig).Spec base := by
  have hse_m1 : signExtend12 (-1 : BitVec 12) = (-1 : Word) := by decide
  have hse_1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  vcgen
  case region => exact ⟨hwf, hrww⟩
  case swrRevLeBe.loop.inv_init =>
    rintro rf ws A ⟨rf₀, ws₀, -,
      ⟨hx10, hx11, hx12, rfl, hol, hlb, hsb, hdb, hdj⟩, rfl, rfl⟩
    simp only [swrRevLeBeInitBlock, execBlock_cons, execBlock_nil, execInstrRF, aluSem]
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
        RegFile.get_set_self _ _ _ (by decide), hx10, hx11]
      simp
    · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
        RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5), hx12]
      simp
    · rw [RegFile.get_set_self _ _ _ (by decide),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x6),
        RegFile.get_set_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5), hx11]
      simp
    · rw [revWin_zero]
  case swrRevLeBe.loop.inv_step =>
    rintro i hi rf' ws' A' ⟨rf₀, ws₀, -,
      ⟨⟨hx5, hx6, hx7, hile, hlb, hol, hsb, hdb, hdj, hwin⟩, -⟩, rfl, rfl⟩
    have hwslen : ws₀.length = len := by rw [hwin]; exact length_revWin bs len orig i hol (by omega)
    simp only [show (swrRevLeBeFn src dst len bs orig).rw.base = dst from rfl,
      show (swrRevLeBeFn src dst len bs orig).region = ⟨src, bs⟩ from rfl]
    rw [swr_step_engine src dst len i bs rf₀ ws₀ hx5 hx6 hi hsb hdb hdj hwslen]
    refine ⟨?_, ?_, ?_, by omega, hlb, hol, hsb, hdb, hdj, ?_⟩
    · rw [swrStepRf_get_x5, hx5, hse_m1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [swrStepRf_get_x6, hx6, hse_1]
      have h1 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [swrStepRf_get_x7, hx7, hse_m1]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      have h2 : (BitVec.ofNat 64 (len - (i + 1))).toNat = len - (i + 1) := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    · rw [hwin, revWin_step bs len orig i hol hi]
  case swrRevLeBe.loop.exhausted =>
    rintro rf ws A ⟨-, -, hx7, hile, -, -, -, -, -, -⟩
    simp only [Cond.holds, not_not]
    rw [hx7]
    have : len - len = 0 := by omega
    rw [show (BitVec.ofNat 64 (len - len)) = (0 : Word) by rw [this]; rfl]
    rfl
  case swrRevLeBe.loop.body.step.mem =>
    rintro rf ws A hwslen ⟨i, hi, ⟨hx5, hx6, hx7, hile, hlb, hol, hsb, hdb, hdj, hwin⟩, -⟩
    have hlen0 : ws.length = len := hwslen
    have hbase : (swrRevLeBeFn src dst len bs orig).rw.base = dst := rfl
    have h2 : (BitVec.ofNat 64 (len - 1 - i)).toNat = len - 1 - i := by
      rw [BitVec.toNat_ofNat]; omega
    -- load address (after x5 decrement) misses the writable window
    have hla : (rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))).get .x5
        + signExtend12 (0 : BitVec 12) = src + BitVec.ofNat 64 (len - 1 - i) := by
      rw [RegFile.get_set_self _ _ _ (by decide), hx5, hse_m1, hse_0]
      have h1 : (BitVec.ofNat 64 (len - i)).toNat = len - i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hnr : ¬ inRw dst ws
        ((rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12))).get .x5
          + signExtend12 (0 : BitVec 12)) 1 := by
      rw [hla]
      unfold inRw
      rw [hlen0]
      have hsubd : (src + BitVec.ofNat 64 (len - 1 - i) - dst).toNat
          = (src.toNat + (len - 1 - i) + (2 ^ 64 - dst.toNat)) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, BitVec.toNat_add, h2]; congr 1; omega
      rw [hsubd]; rcases hdj with hd | hd <;> omega
    have hstore : (rf.get .x6 + signExtend12 (0 : BitVec 12) - dst).toNat = i := by
      rw [hx6, hse_0]
      have hi2 : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
      bv_omega
    have hsub : (src + BitVec.ofNat 64 (len - 1 - i) - src).toNat = len - 1 - i := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, h2]; omega
    rw [show swrRevLeBeStepBlock =
        [.ADDI .x5 .x5 (-1 : BitVec 12), .LBU .x28 .x5 0, .SB .x6 .x28 0,
         .ADDI .x6 .x6 (1 : BitVec 12), .ADDI .x7 .x7 (-1 : BitVec 12)] from rfl,
      show (swrRevLeBeFn src dst len bs orig).region = ⟨src, bs⟩ from rfl, hbase]
    -- ADDI x5 (no memory obligation), thread the register update
    refine ⟨trivial, ?_⟩
    rw [show (execInstrRF ⟨src, bs⟩ dst rf ws (.ADDI .x5 .x5 (-1 : BitVec 12)))
        = (rf.set .x5 (rf.get .x5 + signExtend12 (-1 : BitVec 12)), ws) from rfl]
    -- LBU obligation (routes to the read-only region) ∧ rest
    refine ⟨?_, ?_⟩
    · simp only [loadSem]
      rw [if_neg hnr]
      unfold Region.loadOk
      rw [hla, hsub]
      refine ⟨Nat.one_dvd _, ?_⟩
      show len - 1 - i + 1 ≤ bs.length
      omega
    · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _ hnr]
      -- SB obligation (writable, aligned) ∧ trailing ADDIs (no obligations)
      refine ⟨?_, trivial, trivial, trivial⟩
      dsimp only [storeSem]
      refine ⟨?_, ?_⟩
      · unfold inRw
        rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5), hlen0, hstore]
        omega
      · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28),
          RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5), hstore]
        exact Nat.one_dvd _
  case swrRevLeBe.post =>
    rintro rf ws A ⟨⟨i, hile, hx5, hx6, hx7, hle, hlb, hol, hsb, hdb, hdj, hwin⟩, hncond⟩
    have hi_len : i = len := by
      simp only [Cond.holds, not_not] at hncond
      rw [hx7] at hncond
      have hz : rf.get .x0 = 0 := rfl
      rw [hz] at hncond
      have : (BitVec.ofNat 64 (len - i)).toNat = (0 : Word).toNat := by rw [hncond]
      rw [show (0 : Word).toNat = 0 from rfl, BitVec.toNat_ofNat] at this
      omega
    subst hi_len
    show ws = (bs.take i).reverse
    rw [hwin, revWin_len_eq bs i orig hol hlb]

end SwrRevLeBeSAsm

end EvmAsm.Codegen
