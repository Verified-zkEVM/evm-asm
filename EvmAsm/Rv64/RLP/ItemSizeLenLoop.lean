/-
  EvmAsm.Rv64.RLP.ItemSizeLenLoop

  The long-form length-byte accumulation loop of the codegen guest routine
  `rlp_item_size` (`EvmAsm/Codegen/Programs/RlpRead.lean`, 35 instructions).

  `rlp_item_size` takes `a0` = pointer to one encoded RLP item and returns
  `a0` = the item's FULL encoded size (prefix + payload). For the long forms
  (`0xb8..0xbf` long string, `0xf8..0xff` long list) the payload length is
  itself a big-endian byte field of `lol = prefix - 0xb7` (resp. `- 0xf7`)
  bytes; instructions 25..31 walk that field and accumulate it into `x28`.

  This module verifies exactly that loop, and nothing else:

  ```
    25  base+100  BEQ  x30 x0 +28   ; loop head: count == 0 → exit (idx 32)
    26  base+104  SLLI x28 x28 8    ; acc <<= 8
    27  base+108  LBU  x31 x29 0    ; byte = mem[cursor]
    28  base+112  OR   x28 x28 x31  ; acc |= byte
    29  base+116  ADDI x29 x29 1    ; cursor += 1
    30  base+120  ADDI x30 x30 -1   ; count -= 1
    31  base+124  JAL  x0 -24       ; → idx 25
    32  base+128                    ; loop exit lands here
  ```

  Register roles: counter `x30` (counts down, unsigned), accumulator `x28`,
  byte scratch `x31`, source cursor `x29` (counts up). This is the same seven
  instructions as `rlp_walk_init`'s long-list length loop (`wi_len_loop` in
  `EvmAsm/Rv64/RLP/WalkInit.lean`, idx 17..23) under the renaming
  `x31 ↔ x28` (accumulator ↔ byte scratch) and `x6 → x29` (cursor), so this
  module is a register-renamed port of that proof and reuses the same
  arithmetic substrate (`cu64_step`, `Nat.fromBytesBE_snoc`,
  `word_ofNat_succ_dec`, `word_ofNat_succ_ne_zero`).

  ## Why the program is re-declared here

  `scripts/check-layering.sh` (L1) forbids the verified core from importing
  `EvmAsm.Codegen.*`, so this file cannot name the codegen constant
  `EvmAsm.Codegen.rlpItemSize_prog`. `rlp_item_size_prog` below is the same
  35-instruction list declared core-side, mirroring how
  `EvmAsm.Rv64.RLP.rlp_walk_init_prog` is the core-owned body that
  `EvmAsm/Codegen/Programs/RlpWalk.lean` emits from. A codegen-side consumer
  bridges with `rfl` (`CodeReq.ofProg base rlpItemSize_prog =
  rlp_item_size_code base`), which fails loudly if the two ever drift.
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.RLP.Phase2LongLoopGeneral
import EvmAsm.Rv64.RLP.ContentToU64
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64
open EvmAsm.Rv64.Tactics
open EvmAsm.EL.RLP

/-- The 35-instruction body of the codegen guest `rlp_item_size`, declared
    core-side (see the module docstring for why it is not imported).
    `a0=x10`, `ra=x1`, scratch `t0=x5`, `t1=x6`, `t2=x7`, `t3..t6=x28..x31`. -/
def rlp_item_size_prog : List Instr :=
  [ .LBU .x5 .x10 (0 : BitVec 12),      -- 0  prefix byte
    .LI .x6 (0x80 : Word),              -- 1
    .BGEU .x5 .x6 (12 : BitVec 13),     -- 2  prefix ≥ 0x80 → idx 5
    .LI .x10 (1 : Word),                -- 3  single byte: size = 1
    .JALR .x0 .x1 (0 : BitVec 12),      -- 4
    .LI .x6 (0xb8 : Word),              -- 5
    .BGEU .x5 .x6 (16 : BitVec 13),     -- 6  prefix ≥ 0xb8 → idx 10
    .ADDI .x10 .x5 (-128 : BitVec 12),  -- 7  short string: len = prefix - 0x80
    .ADDI .x10 .x10 (1 : BitVec 12),    -- 8  size = 1 + len
    .JALR .x0 .x1 (0 : BitVec 12),      -- 9
    .LI .x6 (0xc0 : Word),              -- 10
    .BGEU .x5 .x6 (16 : BitVec 13),     -- 11 prefix ≥ 0xc0 → idx 15
    .LI .x6 (0xb7 : Word),              -- 12 long string: lol = prefix - 0xb7
    .SUB .x7 .x5 .x6,                   -- 13
    .JAL .x0 (32 : BitVec 21),          -- 14 → idx 22 (shared long tail)
    .LI .x6 (0xf8 : Word),              -- 15
    .BGEU .x5 .x6 (16 : BitVec 13),     -- 16 prefix ≥ 0xf8 → idx 20
    .ADDI .x10 .x5 (-192 : BitVec 12),  -- 17 short list: len = prefix - 0xc0
    .ADDI .x10 .x10 (1 : BitVec 12),    -- 18 size = 1 + len
    .JALR .x0 .x1 (0 : BitVec 12),      -- 19
    .LI .x6 (0xf7 : Word),              -- 20 long list: lol = prefix - 0xf7
    .SUB .x7 .x5 .x6,                   -- 21
    .LI .x28 (0 : Word),                -- 22 acc = 0
    .ADDI .x29 .x10 (1 : BitVec 12),    -- 23 cursor = ptr + 1
    .MV .x30 .x7,                       -- 24 count = lol
    .BEQ .x30 .x0 (28 : BitVec 13),     -- 25 loop head: count == 0 → idx 32
    .SLLI .x28 .x28 (8 : BitVec 6),     -- 26
    .LBU .x31 .x29 (0 : BitVec 12),     -- 27
    .OR .x28 .x28 .x31,                 -- 28
    .ADDI .x29 .x29 (1 : BitVec 12),    -- 29
    .ADDI .x30 .x30 (-1 : BitVec 12),   -- 30
    .JAL .x0 (-24 : BitVec 21),         -- 31 → idx 25
    .ADDI .x10 .x7 (1 : BitVec 12),     -- 32 size = 1 + lol
    .ADD .x10 .x10 .x28,                -- 33 size += decoded payload length
    .JALR .x0 .x1 (0 : BitVec 12) ]     -- 34

theorem rlp_item_size_prog_length : rlp_item_size_prog.length = 35 := rfl

abbrev rlp_item_size_code (base : Word) : CodeReq :=
  CodeReq.ofProg base rlp_item_size_prog

/-- One iteration of the long-form length loop (idx 26..30), `base+104 → base+124`.
    acc=`x28`, ptr=`x29`, byte=`x31`, count=`x30`. -/
theorem risLenLoopBody (base srcBase x28Old x31Old x30Val : Word)
    (srcBytes : List (BitVec 8)) (si : Nat) (hsalign : srcBase.toNat % 8 = 0)
    (hsi : si < srcBytes.length) (hsover : srcBase.toNat + si < 2 ^ 64)
    (hsvalid : isValidByteAccess (srcBase + BitVec.ofNat 64 si) = true) :
    cpsTripleWithin 5 (base + 104) (base + 124) (rlp_item_size_code base)
      ((.x28 ↦ᵣ x28Old) ** (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) ** (.x31 ↦ᵣ x31Old) **
       (.x30 ↦ᵣ x30Val) ** bytesRegion srcBase srcBytes)
      ((.x28 ↦ᵣ ((x28Old <<< (8 : Nat)) ||| BitVec.setWidth 64 (srcBytes[si]'hsi))) **
       (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
       (.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi)) **
       (.x30 ↦ᵣ (x30Val + signExtend12 (-1 : BitVec 12))) ** bytesRegion srcBase srcBytes) := by
  have hslli := slli_spec_gen_same_within .x28 x28Old (8 : BitVec 6) (base + 104) (by nofun)
  rw [show (8 : BitVec 6).toNat = 8 from by decide] at hslli
  have hlbu := bytesRegion_lbu_within .x31 .x29 srcBase x31Old (base + 108) srcBytes si
    (by decide) hsalign hsi hsover hsvalid
  have hor := or_spec_gen_rd_eq_rs1_within .x28 .x31 (x28Old <<< (8 : Nat))
    (BitVec.setWidth 64 (srcBytes[si]'hsi)) (base + 112) (by nofun)
  have ha29 := addi_spec_gen_same_within .x29 (srcBase + BitVec.ofNat 64 si) 1 (base + 116)
    (by nofun)
  rw [show (srcBase + BitVec.ofNat 64 si) + signExtend12 (1 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (si + 1) from by
        rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]; bv_omega] at ha29
  have ha30 := addi_spec_gen_same_within .x30 x30Val (-1 : BitVec 12) (base + 120) (by nofun)
  runBlock hslli hlbu hor ha29 ha30

/-- The long-form length loop (idx 25..31), `base+100 → base+128`, by induction on
    the counter `x30`; accumulates `x28 = fromBytesBE` of the read length bytes. -/
theorem risLenLoop (base srcBase x31Old : Word) (srcBytes pre : List (BitVec 8)) (si n : Nat)
    (hsalign : srcBase.toNat % 8 = 0)
    (hslen : si + n ≤ srcBytes.length)
    (hsover : srcBase.toNat + (si + n) ≤ 2 ^ 64)
    (hbound : pre.length + n ≤ 8)
    (hsvalid : ∀ k, k < n → isValidByteAccess (srcBase + BitVec.ofNat 64 (si + k)) = true) :
    cpsTripleWithin (7 * n + 1) (base + 100) (base + 128) (rlp_item_size_code base)
      ((.x30 ↦ᵣ BitVec.ofNat 64 n) ** (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
       (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
      ((.x30 ↦ᵣ (0 : Word)) ** (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + n))) **
       (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ (srcBytes.drop si).take n))) **
       regOwn .x31 ** (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) := by
  have hmono : ∀ a i, CodeReq.singleton (base + 100) (.BEQ .x30 .x0 (28 : BitVec 13)) a = some i
      → rlp_item_size_code base a = some i :=
    CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_item_size_prog 25 (base + 100)
      (by rw [rlp_item_size_prog_length]; norm_num)
      (by rw [rlp_item_size_prog_length]; norm_num) (by bv_omega))
  have ha_t : (base + 100) + signExtend13 (28 : BitVec 13) = base + 128 := by
    rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]; bv_omega
  have ha_f : (base + 100 : Word) + 4 = base + 104 := by bv_omega
  induction n generalizing si pre x31Old with
  | zero =>
    have hbeq := beq_spec_gen_within .x30 .x0 (28 : BitVec 13) (BitVec.ofNat 64 0) (0 : Word)
      (base + 100)
    rw [ha_t, ha_f] at hbeq
    have htaken := cpsBranchWithin_takenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQf => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQf
        exact ((sepConj_pure_right _).1 h_pure).2 (by decide))
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hq => ?_) htaken
    rw [show (0#64 : Word) = 0 from by decide] at hq
    simp only [Nat.add_zero, List.take_zero, List.append_nil]
    have hq1 := sepConj_mono_left
      (sepConj_mono_right (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hq
    have hq2 := sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (regIs_implies_regOwn .x31))))
      h hq1
    xperm_hyp hq2
  | succ k ih =>
    have hbeq := beq_spec_gen_within .x30 .x0 (28 : BitVec 13) (BitVec.ofNat 64 (k + 1))
      (0 : Word) (base + 100)
    rw [ha_t, ha_f] at hbeq
    have hne : BitVec.ofNat 64 (k + 1) ≠ (0 : Word) := word_ofNat_succ_ne_zero k (by omega)
    have hA1 := cpsBranchWithin_ntakenPath
      (cpsBranchWithin_extend_code hmono (cpsBranchWithin_frameR
        ((.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 si)) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE pre)) ** (.x31 ↦ᵣ x31Old) **
         bytesRegion srcBase srcBytes)
        (by pcFree) hbeq))
      (fun hp hQt => by
        obtain ⟨_, _, _, _, ⟨_, _, _, _, _, h_pure⟩, _⟩ := hQt
        exact hne ((sepConj_pure_right _).1 h_pure).2)
    have hsi0 : si < srcBytes.length := by omega
    have hprelt : Nat.fromBytesBE pre < 2 ^ 56 := by
      have := Nat.fromBytesBE_lt pre
      have hpl : pre.length ≤ 7 := by omega
      calc Nat.fromBytesBE pre < 256 ^ pre.length := this
        _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hpl
        _ = 2 ^ 56 := by norm_num
    have hx28tn : (BitVec.ofNat 64 (Nat.fromBytesBE pre)).toNat = Nat.fromBytesBE pre := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have body := risLenLoopBody base srcBase (BitVec.ofNat 64 (Nat.fromBytesBE pre)) x31Old
      (BitVec.ofNat 64 (k + 1)) srcBytes si hsalign hsi0 (by omega) (hsvalid 0 (by omega))
    rw [word_ofNat_succ_dec k] at body
    have hbnd : Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 2 ^ 64 := by
      have h := Nat.fromBytesBE_lt (pre ++ [srcBytes[si]'hsi0])
      simp only [List.length_append, List.length_singleton] at h
      calc Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]) < 256 ^ (pre.length + 1) := h
        _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 64 := by norm_num
    have hacc :
        ((BitVec.ofNat 64 (Nat.fromBytesBE pre) <<< (8 : Nat)) |||
            BitVec.setWidth 64 (srcBytes[si]'hsi0))
          = BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0])) := by
      apply BitVec.eq_of_toNat_eq
      rw [cu64_step _ _ (by rw [hx28tn]; exact hprelt), hx28tn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hbnd, Nat.fromBytesBE_snoc]
    rw [hacc] at body
    have body_x0 := cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word))) (by pcFree) body
    have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (base + 124)
    have ha_back : (base + 124) + signExtend21 (-24 : BitVec 21) = base + 100 := by
      rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]; bv_omega
    rw [ha_back] at hjal
    have hjal_mono : ∀ a i, CodeReq.singleton (base + 124) (.JAL .x0 (-24 : BitVec 21)) a = some i
        → rlp_item_size_code base a = some i :=
      CodeReq.singleton_mono (CodeReq.ofProg_lookup_addr base rlp_item_size_prog 31 (base + 124)
        (by rw [rlp_item_size_prog_length]; norm_num)
        (by rw [rlp_item_size_prog_length]; norm_num) (by bv_omega))
    have hjal_ext := cpsTripleWithin_extend_code hjal_mono hjal
    have hjal_S : cpsTripleWithin 1 (base + 124) (base + 100) (rlp_item_size_code base)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x30 ↦ᵣ BitVec.ofNat 64 k) ** (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
        ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
         (.x30 ↦ᵣ BitVec.ofNat 64 k) ** (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
         (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
         (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes) :=
      cpsTripleWithin_weaken
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (fun h hp => by simpa only [sepConj_emp_left'] using hp)
        (cpsTripleWithin_frameR
          ((.x31 ↦ᵣ BitVec.setWidth 64 (srcBytes[si]'hsi0)) **
           (.x30 ↦ᵣ BitVec.ofNat 64 k) ** (.x29 ↦ᵣ (srcBase + BitVec.ofNat 64 (si + 1))) **
           (.x28 ↦ᵣ BitVec.ofNat 64 (Nat.fromBytesBE (pre ++ [srcBytes[si]'hsi0]))) **
           (.x0 ↦ᵣ (0 : Word)) ** bytesRegion srcBase srcBytes)
          (by pcFree) hjal_ext)
    have hsvalid' :
        ∀ j, j < k → isValidByteAccess (srcBase + BitVec.ofNat 64 ((si + 1) + j)) = true := by
      intro j hj
      have h := hsvalid (j + 1) (by omega)
      rwa [show si + (j + 1) = (si + 1) + j from by omega] at h
    have ihspec := ih (si := si + 1) (pre := pre ++ [srcBytes[si]'hsi0])
      (x31Old := BitVec.setWidth 64 (srcBytes[si]'hsi0)) (by omega) (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega) hsvalid'
    have s12 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by
      have hp2 := sepConj_mono_left (sepConj_mono_right
        (fun h' hp' => ((sepConj_pure_right h').1 hp').1)) h hp
      xperm_hyp hp2) hA1 body_x0
    have s123 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s12 hjal_S
    have s1234 := cpsTripleWithin_seq_perm_same_cr (fun h hp => by xperm_hyp hp) s123 ihspec
    have hslice : pre ++ (srcBytes.drop si).take (k + 1)
        = (pre ++ [srcBytes[si]'hsi0]) ++ (srcBytes.drop (si + 1)).take k := by
      rw [List.drop_eq_getElem_cons hsi0, List.take_succ_cons, List.append_assoc,
        List.singleton_append]
    rw [show 7 * (k + 1) + 1 = 1 + 5 + 1 + (7 * k + 1) from by ring,
        show si + (k + 1) = (si + 1) + k from by omega, hslice]
    exact cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp) (fun h hp => by xperm_hyp hp) s1234

end EvmAsm.Rv64.RLP
