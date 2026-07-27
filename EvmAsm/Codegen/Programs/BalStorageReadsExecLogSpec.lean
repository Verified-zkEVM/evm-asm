/-
  EvmAsm.Codegen.Programs.BalStorageReadsExecLogSpec

  Verified triple for `bal_storage_reads_in_exec_log` (bead evm-asm-4ch8f.43.1)
  — the first BAL-vs-exec consistency validator port.  EIP-7928 `storage_reads`
  (slots accessed but not net-changed) are committed via the block access-list
  hash but do NOT affect the state root, so they are not covered by the
  post-state-root comparison; this routine rejects a BAL that fabricates a
  read of a slot the account never accessed, by checking every claimed read
  against the persistent exec SLOAD log.

  Architecture (within-level, additive — no `Ast`/`Vc`/`StmtSound` changes):

  * the routine is EXACTLY an `AbiFrame.abiFrameProg` instance (kernel-checked
    below): `addi sp,sp,-64` + 8 saves, a 92-instruction body, the shared
    8-load epilogue + `ret` — so `abiFrame_spec` discharges the frame and the
    whole obligation is the BODY triple;
  * the body's callees are `rlp_walk_init` / `rlp_walk_next` only, both already
    verified (`rlp_walk_init_spec_within` / `rlp_walk_next_spec_within`),
    composed at each `jal` site via `WP.cpsCallWithin`;
  * loop shapes (fed to bead .70.4): outer reads loop = head-test whileBreak
    (idx 32, `beq s3,s4` exits to the match stub) whose body contains the
    call + two inner loops; byte-reverse loop = countdown (idx 55–61);
    log scan loop = bottom-test pointer countdown (idx 68–95, `bne x28,x9`
    back-edge) with an 8-dword compare cascade whose mismatch arms all join
    the scan-next station (idx 93); every parse-fail branch is a straight
    branch into the shared reject stub (idx 100, `li a0,1`, falls through to
    the epilogue) and the match stub (idx 98–99) is `liJumpTailProg
    [(a0,0)] (+8)` jumping over it — the jump-join tail shape (PR #10115).

  Program geometry (instruction slots, byte offset = 4·slot):

     0      addi sp, sp, -64
     1–8    sd ra/s0/s1/s2/s3/s4/s5/s6, 0/8/…/56(sp)
     9–14   mv s0,a0 ; mv s1,a3 ; mv s2,a4 ; mv s5,a5 ; mv a0,a1 ; mv a1,a2
            (s5 = the ENTRY STRIDE argument, a5 — parked in a callee-saved
             register because the rlp_walk_* calls clobber a5; GH #10619)
    15      jal rlp_walk_init            (AccountChanges outer list)
    16      bnez a2 → 100
    17      mv s6, a1                    (account end)
    18/21/24  jal rlp_walk_next          (items 0,1,2; 19/22/25 bnez a1 → 100)
    20/23   mv a1, s6
    26–27   sub a0,a0,a2 ; mv a1,a2      (storage_reads content window)
    28      jal rlp_walk_init            (29 bnez a2 → 100)
    30–31   mv s3,a0 ; mv s4,a1          (reads cursor / end)
    32      beq s3,s4 → 98               (OUTER LOOP HEAD; exhausted = accept)
    33–34   mv a0,s3 ; mv a1,s4
    35      jal rlp_walk_next            (36 bnez a1 → 100)
    37      mv s3,a0
    38–39   sub t1,a0,a2 ; mv t2,a2      (key content ptr / len)
    40–41   li t0,32 ; bltu t0,t2 → 100  (len > 32 rejects)
    42–44   beqz t2 → 45 ; lbu t0,(t1) ; beqz t0 → 100   (leading-0 rejects)
    45–46   la t0, bsr_krev
    47–50   sd x0, 0/8/16/24(t0)         (zero the 32-byte scratch)
    51–54   add x28,t1,t2 ; addi x28,-1 ; mv x29,t0 ; mv x30,t2
    55      beqz x30 → 62                (REV LOOP HEAD)
    56–60   lbu x15,(x28) ; sb x15,(x29) ; x28-- ; x29++ ; x30--
    61      j 55
    62–63   mv t2,s2 ; beqz t2 → 100     (empty log but a read claimed)
    64–65   mul x28,t2,s5 ; add x28,s1,x28   (past-last log entry)
    66–67   la x31, bsr_krev
    68      sub x28, x28, s5             (SCAN LOOP HEAD: step to prev entry)
    69–92   8 × (ld/ld/bne → 94)         (addr 4 dwords, then key 4 dwords)
    93      j 97                         (all 8 matched → advance)
    94–95   mv x29,s1 ; bne x28,x29 → 68 (not at first entry → keep scanning)
    96      j 100                        (whole log scanned; slot absent)
    97      j 32                         (advance: next claimed read)
    98–99   li a0,0 ; j 101              (match stub = liJumpTailProg)
   100      li a0,1                      (reject stub; falls through)
   101–109  ld ra/s0/…/s6 ; addi sp,sp,64
   110      ret
-/

import EvmAsm.Codegen.Programs.BalStorageReadsExecLog
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.RetFromLoop
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.AccumLoop
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Rv64.WP.Call
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.RLP

namespace BalStorageReadsExecLogSpec

/-! ## §1  Geometry: the routine IS an `abiFrameProg` instance -/

/-- The emitted program at `List Instr` (the `Program` alias is a plain `def`,
    opaque to `GetElem`). -/
def bsreProg : List Instr := balStorageReadsInExecLog_prog

/-- The ABI frame descriptor: `ra` at 0, then s0/s1/s2/s3/s4/s5/s6. -/
def bsreFrame : FrameDesc :=
  [((.x1 : Reg), (0 : BitVec 12)), (.x8, 8), (.x9, 16), (.x18, 24),
   (.x19, 32), (.x20, 40), (.x21, 48), (.x22, 56)]

/-- The 92-instruction body between the prologue and the shared epilogue. -/
def bsreBody : List Instr := (bsreProg.drop 9).take 92

/-- **The frame decomposition** — the whole routine is byte-for-byte an
    `abiFrameProg` instance, so `abiFrame_spec` owns the frame reasoning. -/
theorem bsre_prog_eq_abiFrame :
    bsreProg = abiFrameProg (-64 : BitVec 12) (64 : BitVec 12) bsreFrame bsreBody := by
  decide +kernel

#guard bsreBody.length = 92

-- Loop / stub geometry pins (relative slots; byte offsets in the branch
-- immediates are 4× these).
-- Outer loop head: exhausted-cursor accept exit to the match stub.
#guard bsreProg[32]? = some (.BEQ .x19 .x20 (264 : BitVec 13))
#guard 4 * 32 + 264 = 4 * 98
-- Rev loop: head test + back-edge.
#guard bsreProg[55]? = some (.BEQ .x30 .x0 (28 : BitVec 13))
#guard 4 * 55 + 28 = 4 * 62
#guard bsreProg[61]? = some (.JAL .x0 (-24 : BitVec 21))
#guard 4 * 61 - 24 = 4 * 55
-- Scan loop: entry-step, compare-cascade join, pointer-test back-edge,
-- absent-exit, advance back-edge.
-- The cursor step subtracts the STRIDE REGISTER (`x21`, loaded from the `a5`
-- argument), not a baked-in 128, so a caller cannot re-point the scan at another
-- log without also supplying that log's entry width (GH #10619).
#guard bsreProg[68]? = some (.SUB .x28 .x28 .x21)
#guard bsreProg[64]? = some (.MUL .x28 .x7 .x21)   -- count × stride = past-last-entry
#guard bsreProg[12]? = some (.MV .x21 .x15)        -- a5 → s5, parked across the calls
#guard bsreProg[93]? = some (.JAL .x0 (16 : BitVec 21))   -- 8/8 matched → advance
#guard 4 * 93 + 16 = 4 * 97
#guard bsreProg[95]? = some (.BNE .x28 .x29 (-108 : BitVec 13))  -- scan back-edge
#guard 4 * 95 - 108 = 4 * 68
#guard bsreProg[96]? = some (.JAL .x0 (16 : BitVec 21))   -- whole log scanned → reject
#guard 4 * 96 + 16 = 4 * 100
#guard bsreProg[97]? = some (.JAL .x0 (-260 : BitVec 21)) -- advance → outer head
#guard 4 * 97 - 260 = 4 * 32
-- The accept stub IS the jump-join tail combinator's byte shape, jumping
-- over the reject stub into the shared epilogue.
#guard (bsreProg.drop 98).take 3
  = liJumpTailProg [(.x10, (0 : Word))] (8 : BitVec 21) ++ [.LI .x10 (1 : Word)]
#guard 4 * 99 + 8 = 4 * 101
-- Exactly ONE ret; the shared epilogue starts at slot 101.
#guard (bsreProg.filter
  (fun i => i = Instr.JALR .x0 .x1 (0 : BitVec 12))).length = 1
#guard bsreProg[101]? = some (.LD .x1 .x2 (0 : BitVec 12))
#guard bsreProg[110]? = some (.JALR .x0 .x1 (0 : BitVec 12))

/-! ## §2  The genuine functional spec

    The post is stated against the SAME abstraction the verified callees
    export — `rlpItemDecode` (WalkNext.lean) for per-item parses — plus a
    direct byte-slice model of the 128-byte exec-log entries. -/

/-- The 32-byte EVM-stack-order (LE-limb) image of a big-endian minimal key:
    left-pad to 32 with zeros, then byte-reverse — equivalently, reverse the
    content and right-pad with zeros.  This is exactly what the byte-reverse
    loop materialises in `bsr_krev`. -/
def keyRev32 (key : List (BitVec 8)) : List (BitVec 8) :=
  key.reverse ++ List.replicate (32 - key.length) 0

@[simp] theorem keyRev32_length (key : List (BitVec 8)) (h : key.length ≤ 32) :
    (keyRev32 key).length = 32 := by
  simp [keyRev32]; omega

/-- Exec-log entry field (Storage.lean layout): entry `i` occupies bytes
    `[128*i, 128*(i+1))`; `addrHash` at +0, `slotKey` at +32. -/
def logSlice (log : List (BitVec 8)) (i off n : Nat) : List (BitVec 8) :=
  (log.drop (128 * i + off)).take n

/-- Entry `i` of the exec log is keyed on `addr` (the 32-byte addrHash the
    caller passes) with slot key `key32` (32 bytes, EVM-stack order). -/
def entryMatches (log : List (BitVec 8)) (i : Nat)
    (addr key32 : List (BitVec 8)) : Prop :=
  logSlice log i 0 32 = addr ∧ logSlice log i 32 32 = key32

/-- The exec log records an access of `key32` by `addr` (in any of its
    `count` entries). -/
def logHasRead (log : List (BitVec 8)) (count : Nat)
    (addr key32 : List (BitVec 8)) : Prop :=
  ∃ i, i < count ∧ entryMatches log i addr key32

/-- One storage_reads item at offset `off` inside the AccountChanges bytes:
    the RLP item decode (per the verified walker's semantics), its content
    window, and the routine's canonicality guards (≤ 32 bytes, no leading
    zero byte). -/
def readItemAt (bytes : List (BitVec 8)) (base endPtr : Word) (off : Nat)
    (next len : Word) : Prop :=
  rlpItemDecode bytes off (base + BitVec.ofNat 64 off) endPtr next len ∧
  len.toNat ≤ 32 ∧
  (len ≠ (0 : Word) →
    ∃ b, bytes[(next - len - base).toNat]? = some b ∧ b ≠ (0 : BitVec 8))

/-- The content bytes of the item decoded by `readItemAt`: the `len`-byte
    window ending at the advanced cursor (`content_ptr = next - len`, the
    walker's caller-side invariant). -/
def readKeyBytes (bytes : List (BitVec 8)) (base : Word) (next len : Word) :
    List (BitVec 8) :=
  (bytes.drop (next - len - base).toNat).take len.toNat

/-- **The success derivation**: walking the storage_reads window from byte
    offset `off` (cursor `base + off`) up to `endPtr`, every claimed read
    parses canonically and its slot key appears in the exec log keyed on
    `addr`.  Terminates by `next` strictly advancing (`rlpItemDecode` forces
    cursor < endPtr on every accepting form). -/
inductive ReadsOk (bytes : List (BitVec 8)) (base endPtr : Word)
    (log : List (BitVec 8)) (count : Nat) (addr : List (BitVec 8)) :
    Nat → Prop
  | done (off : Nat) (h : base + BitVec.ofNat 64 off = endPtr) :
      ReadsOk bytes base endPtr log count addr off
  | step (off : Nat) (next len : Word)
      (hne : base + BitVec.ofNat 64 off ≠ endPtr)
      (hitem : readItemAt bytes base endPtr off next len)
      (hfound : logHasRead log count addr
        (keyRev32 (readKeyBytes bytes base next len)))
      (hrest : ReadsOk bytes base endPtr log count addr (next - base).toNat) :
      ReadsOk bytes base endPtr log count addr off

/-! ## §3  The verdict stubs

    Both stubs end at the shared epilogue entry (slot 101, `base + 404`) —
    the BODY exit in the `abiFrame_spec` architecture, so these are plain
    two/one instruction triples, not `ret`-reaching tails. -/

/-- The accept stub (slots 98–99): `li a0, 0 ; j +8` jumps over the reject
    stub into the shared epilogue with the verdict pinned. -/
theorem bsre_matchTail_spec (base vOld : Word)
    (hbound : 4 * bsreProg.length < 2 ^ 64) :
    cpsTripleWithin 2 (base + 392) (base + 404)
      (CodeReq.ofProg base bsreProg)
      ((.x10 : Reg) ↦ᵣ vOld) ((.x10 : Reg) ↦ᵣ (0 : Word)) := by
  have hli := liftCode (cr' := CodeReq.ofProg base bsreProg)
    (li_spec_gen_within .x10 vOld (0 : Word) (base + 392) (by decide))
    (CodeReq.ofProg_mem_at base (base + 392) bsreProg 98 (.LI .x10 (0 : Word))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 392 + 4 = base + 396 from by bv_omega] at hli
  have hjal := liftCode (cr' := CodeReq.ofProg base bsreProg)
    (jal_x0_spec_gen_within (8 : BitVec 21) (base + 396))
    (CodeReq.ofProg_mem_at base (base + 396) bsreProg 99 (.JAL .x0 (8 : BitVec 21))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 396 + signExtend21 (8 : BitVec 21) = base + 404 from by
    rw [show signExtend21 (8 : BitVec 21) = (8 : Word) from by decide]
    bv_omega] at hjal
  have hjalF := cpsTripleWithin_frameL ((.x10 : Reg) ↦ᵣ (0 : Word))
    pcFree_regIs hjal
  rw [sepConj_emp_right'] at hjalF
  exact cpsTripleWithin_seq_same_cr hli hjalF

/-- The reject stub (slot 100): `li a0, 1`, falling through into the shared
    epilogue with the verdict pinned. -/
theorem bsre_rejectTail_spec (base vOld : Word)
    (hbound : 4 * bsreProg.length < 2 ^ 64) :
    cpsTripleWithin 1 (base + 400) (base + 404)
      (CodeReq.ofProg base bsreProg)
      ((.x10 : Reg) ↦ᵣ vOld) ((.x10 : Reg) ↦ᵣ (1 : Word)) := by
  have hli := liftCode (cr' := CodeReq.ofProg base bsreProg)
    (li_spec_gen_within .x10 vOld (1 : Word) (base + 400) (by decide))
    (CodeReq.ofProg_mem_at base (base + 400) bsreProg 100 (.LI .x10 (1 : Word))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 400 + 4 = base + 404 from by bv_omega] at hli
  exact hli


/-! ## §4  The byte-reverse loop (slots 55–61)

    Materialises `keyRev32 key` in the (pre-zeroed) `bsr_krev` scratch: the
    `klen`-byte big-endian key content is copied byte-reversed into the low
    bytes; the zero suffix from the pre-zeroing survives. -/

/-- The reverse-copy scratch state after `i` copied bytes. -/
def revState (key : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  key.reverse.take i ++ List.replicate (32 - i) 0

@[simp] theorem revState_zero (key : List (BitVec 8)) :
    revState key 0 = List.replicate 32 0 := by
  simp [revState]

theorem revState_full (key : List (BitVec 8)) (_h : key.length ≤ 32) :
    revState key key.length = keyRev32 key := by
  simp [revState, keyRev32, List.take_of_length_le,
    List.length_reverse]

/-- The loop invariant at the header (slot 55), after `i` of `klen` bytes.
    `contentOff`/`klen` locate the key inside the AccountChanges bytes;
    `key` is that content window.  The `x28` source cursor is stated in
    all-`BitVec` arithmetic (`… - 1 - ofNat i`, not `ofNat (… - 1 - i)`):
    the final `ADDI x28, x28, -1` at `i + 1 = klen` steps the cursor to
    `acctBase + contentOff - 1`, which underflows the NAT subtraction when
    `contentOff = 0` but is perfectly consistent as a `BitVec` value. -/
def revInv (acctBase krevBase : Word) (acctBytes : List (BitVec 8))
    (contentOff klen : Nat) (F : Assertion) (i : Nat) : Assertion :=
  ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1 - BitVec.ofNat 64 i)) **
  ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
  ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x15 **
  bytesRegion acctBase acctBytes **
  bytesRegion krevBase
    (revState ((acctBytes.drop contentOff).take klen) i) **
  F

/-! ### §4.1  List-layer helpers -/

theorem revState_length (key : List (BitVec 8)) (i : Nat)
    (h1 : i ≤ key.length) (h2 : i ≤ 32) :
    (revState key i).length = 32 := by
  simp [revState]
  omega

/-- Truncating a zero-extended byte recovers the byte (the `LBU`→`SB`
    value round-trip). -/
theorem zext64_truncate8 (b : BitVec 8) :
    ((b.zeroExtend 64).truncate 8) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j
  simp

/-- Writing byte `i` of the reverse-copy state stores `key.reverse[i]`
    and advances the state. -/
theorem revState_set (key : List (BitVec 8)) (i : Nat) (hi : i < key.length)
    (hlen : key.length ≤ 32) :
    (revState key i).set i (key.reverse[i]'(by simpa using hi))
      = revState key (i + 1) := by
  have hrev : i < key.reverse.length := by simpa using hi
  have hlen_take : (key.reverse.take i).length = i := by
    simp
    omega
  have htake : key.reverse.take (i + 1)
      = key.reverse.take i ++ [key.reverse[i]'hrev] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hrev]
    rfl
  have hrep : List.replicate (32 - i) (0 : BitVec 8)
      = (0 : BitVec 8) :: List.replicate (32 - (i + 1)) 0 := by
    rw [← List.replicate_succ]
    congr 1
    omega
  unfold revState
  rw [hrep, htake, List.set_append, if_neg (by omega), hlen_take,
    Nat.sub_self, List.set_cons_zero, List.append_assoc]
  rfl

/-- The byte the loop reads at iteration `i` IS `key.reverse[i]` for
    `key` the content window. -/
theorem rev_key_byte (acctBytes : List (BitVec 8)) (contentOff klen i : Nat)
    (hi : i < klen) (hcw : contentOff + klen ≤ acctBytes.length) :
    ((acctBytes.drop contentOff).take klen).reverse[i]'(by simp; omega)
      = acctBytes[contentOff + klen - 1 - i]'(by omega) := by
  rw [List.getElem_reverse]
  rw [List.getElem_take, List.getElem_drop]
  congr 1
  simp
  omega

/-- The `SB` step at iteration `i` (value = the `LBU`-loaded, zero-extended
    source byte) advances the reverse-copy state. -/
theorem revState_set_byte (acctBytes : List (BitVec 8)) (contentOff klen i : Nat)
    (hi : i < klen) (hklen : klen ≤ 32) (hcw : contentOff + klen ≤ acctBytes.length) :
    (revState ((acctBytes.drop contentOff).take klen) i).set i
      (((acctBytes[contentOff + klen - 1 - i]'(by omega)).zeroExtend 64).truncate 8)
      = revState ((acctBytes.drop contentOff).take klen) (i + 1) := by
  rw [zext64_truncate8,
    ← rev_key_byte acctBytes contentOff klen i hi hcw]
  exact revState_set _ i (by simp; omega) (by simp; omega)

/-! ### §4.2  Address / counter bridges (symbolic base) -/

private theorem rev_ctr_ne_zero (klen i : Nat) (hi : i < klen) (hk : klen ≤ 32) :
    ¬ (BitVec.ofNat 64 (klen - i) = (0 : Word)) := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at this
  omega

private theorem rev_ctr_dec (klen i : Nat) (hi : i < klen) :
    BitVec.ofNat 64 (klen - i) + signExtend12 (-1 : BitVec 12)
      = BitVec.ofNat 64 (klen - (i + 1)) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show ((-1 : Word)).toNat = 18446744073709551615 from rfl]
  omega

/-- The `BitVec`-form source cursor equals the `Nat`-index form WHILE the
    loop is running (`i < klen`; the two diverge only at `i = klen` with
    `contentOff = 0`, where the `Nat` subtraction truncates). -/
private theorem rev_src_eq (acctBase : Word) (contentOff klen i : Nat)
    (hi : i < klen) :
    acctBase + BitVec.ofNat 64 (contentOff + klen) - 1 - BitVec.ofNat 64 i
      = acctBase + BitVec.ofNat 64 (contentOff + klen - 1 - i) := by
  bv_omega

private theorem rev_src_dec (acctBase : Word) (contentOff klen i : Nat)
    (_hi : i < klen) (_hk : klen ≤ 32) :
    acctBase + BitVec.ofNat 64 (contentOff + klen) - 1 - BitVec.ofNat 64 i
        + signExtend12 (-1 : BitVec 12)
      = acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide]
  bv_omega

private theorem rev_dst_advance (p : Word) (i : Nat) :
    p + BitVec.ofNat 64 i + signExtend12 (1 : BitVec 12)
      = p + BitVec.ofNat 64 (i + 1) := by
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide]
  bv_omega

/-! ### §4.3  One loop iteration (slots 55–61, header back to header) -/

/-- One byte-reverse iteration: header guard (never taken at `i < klen`),
    `LBU` from the descending source cursor, `SB` to the ascending dest
    cursor, three `ADDI` cursor/counter updates, `JAL` back — invariant
    advanced. -/
theorem bsre_revIter_spec (base acctBase krevBase : Word)
    (acctBytes : List (BitVec 8)) (contentOff klen : Nat) (F : Assertion)
    (hF : F.pcFree)
    (halignA : acctBase.toNat % 8 = 0) (halignK : krevBase.toNat % 8 = 0)
    (hcw : contentOff + klen ≤ acctBytes.length) (hklen : klen ≤ 32)
    (hoverA : acctBase.toNat + acctBytes.length ≤ 2 ^ 64)
    (hoverK : krevBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidA : ∀ k, k < acctBytes.length →
      isValidByteAccess (acctBase + BitVec.ofNat 64 k) = true)
    (hvalidK : ∀ k, k < 32 →
      isValidByteAccess (krevBase + BitVec.ofNat 64 k) = true)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (i : Nat) (hi : i < klen) :
    cpsTripleWithin 7 (base + 220) (base + 220)
      (CodeReq.ofProg base bsreProg)
      (revInv acctBase krevBase acctBytes contentOff klen F i)
      (revInv acctBase krevBase acctBytes contentOff klen F (i + 1)) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  have hidx : contentOff + klen - 1 - i < acctBytes.length := by omega
  have hrkl : (revState ((acctBytes.drop contentOff).take klen) i).length = 32 :=
    revState_length _ i (by simp; omega) (by omega)
  unfold revInv
  -- peel this iteration's scratch register x15
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (r := .x15)
      (P := ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
              - BitVec.ofNat 64 i)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) i) **
        F)
      (fun v15 => ?_))
  -- ---- the body instructions ----
  have hlbu := liftCode (cr' := CR)
    (bytesRegion_lbu_within .x15 .x28 acctBase v15 (base + 224) acctBytes
      (contentOff + klen - 1 - i) (by decide) halignA hidx (by omega)
      (hvalidA _ hidx))
    (CodeReq.ofProg_mem_at base (base + 224) bsreProg 56
      (.LBU .x15 .x28 (0 : BitVec 12))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [← rev_src_eq acctBase contentOff klen i hi,
      show base + 224 + 4 = base + 228 from by bv_omega] at hlbu
  have hsb := liftCode (cr' := CR)
    (bytesRegion_sb_within .x29 .x15 krevBase
      ((acctBytes[contentOff + klen - 1 - i]'hidx).zeroExtend 64) (base + 228)
      (revState ((acctBytes.drop contentOff).take klen) i) i halignK
      (by omega) (by omega) (hvalidK i (by omega)))
    (CodeReq.ofProg_mem_at base (base + 228) bsreProg 57
      (.SB .x29 .x15 (0 : BitVec 12))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [revState_set_byte acctBytes contentOff klen i hi hklen hcw,
      show base + 228 + 4 = base + 232 from by bv_omega] at hsb
  have haddi28 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x28
      (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1 - BitVec.ofNat 64 i)
      (-1 : BitVec 12) (base + 232) (by decide))
    (CodeReq.ofProg_mem_at base (base + 232) bsreProg 58
      (.ADDI .x28 .x28 (-1 : BitVec 12))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [rev_src_dec acctBase contentOff klen i hi hklen,
      show base + 232 + 4 = base + 236 from by bv_omega] at haddi28
  have haddi29 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x29 (krevBase + BitVec.ofNat 64 i)
      (1 : BitVec 12) (base + 236) (by decide))
    (CodeReq.ofProg_mem_at base (base + 236) bsreProg 59
      (.ADDI .x29 .x29 (1 : BitVec 12))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [rev_dst_advance krevBase i,
      show base + 236 + 4 = base + 240 from by bv_omega] at haddi29
  have haddi30 := liftCode (cr' := CR)
    (addi_spec_gen_same_within .x30 (BitVec.ofNat 64 (klen - i))
      (-1 : BitVec 12) (base + 240) (by decide))
    (CodeReq.ofProg_mem_at base (base + 240) bsreProg 60
      (.ADDI .x30 .x30 (-1 : BitVec 12))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [rev_ctr_dec klen i hi,
      show base + 240 + 4 = base + 244 from by bv_omega] at haddi30
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (-24 : BitVec 21) (base + 244))
    (CodeReq.ofProg_mem_at base (base + 244) bsreProg 61
      (.JAL .x0 (-24 : BitVec 21))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 244 + signExtend21 (-24 : BitVec 21) = base + 220 from by
    rw [show signExtend21 (-24 : BitVec 21) = (-24 : Word) from by decide]
    bv_omega] at hjal
  -- ---- frames + chain of the body (from base + 224) ----
  have hlbuF := cpsTripleWithin_frameR
    (((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) i) **
      F)
    (by pcf; exact hF) hlbu
  have hsbF := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
        - BitVec.ofNat 64 i)) **
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion acctBase acctBytes **
      F)
    (by pcf; exact hF) hsb
  have haddi28F := cpsTripleWithin_frameR
    (((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x15 : Reg) ↦ᵣ ((acctBytes[contentOff + klen - 1 - i]'hidx).zeroExtend 64)) **
      bytesRegion acctBase acctBytes **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) (i + 1)) **
      F)
    (by pcf; exact hF) haddi28
  have haddi29F := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
        - BitVec.ofNat 64 (i + 1))) **
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x15 : Reg) ↦ᵣ ((acctBytes[contentOff + klen - 1 - i]'hidx).zeroExtend 64)) **
      bytesRegion acctBase acctBytes **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) (i + 1)) **
      F)
    (by pcf; exact hF) haddi29
  have haddi30F := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
        - BitVec.ofNat 64 (i + 1))) **
      ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 (i + 1))) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x15 : Reg) ↦ᵣ ((acctBytes[contentOff + klen - 1 - i]'hidx).zeroExtend 64)) **
      bytesRegion acctBase acctBytes **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) (i + 1)) **
      F)
    (by pcf; exact hF) haddi30
  have hjalF := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
        - BitVec.ofNat 64 (i + 1))) **
      ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 (i + 1))) **
      ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - (i + 1))) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x15 : Reg) ↦ᵣ ((acctBytes[contentOff + klen - 1 - i]'hidx).zeroExtend 64)) **
      bytesRegion acctBase acctBytes **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) (i + 1)) **
      F)
    (by pcf; exact hF) hjal
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hlbuF hsbF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 haddi28F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc2 haddi29F
  have hc4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc3 haddi30F
  have hc5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by
      rw [sepConj_emp_left']
      xperm_hyp hp) hc4 hjalF
  -- ---- header guard station (never taken at i < klen) ----
  have hbrHdr := cpsBranchWithin_frameR
    (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
        - BitVec.ofNat 64 i)) **
      ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
      ((.x15 : Reg) ↦ᵣ v15) **
      bytesRegion acctBase acctBytes **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) i) **
      F)
    (by pcf; exact hF)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x30 .x0 (28 : BitVec 13)
        (BitVec.ofNat 64 (klen - i)) (0 : Word) (base + 220))
      (hmono := CodeReq.ofProg_mem_at base (base + 220) bsreProg 55
        (.BEQ .x30 .x0 (28 : BitVec 13))
        rfl (by decide +kernel) (by decide +kernel) hbound))
  rw [show base + 220 + signExtend13 (28 : BitVec 13) = base + 248 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega,
      show base + 220 + 4 = base + 224 from by bv_omega] at hbrHdr
  -- the body must re-own x15 into the invariant
  have hbody : cpsTripleWithin 6 (base + 224) (base + 220) CR
      (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 i)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x15 : Reg) ↦ᵣ v15) **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) i) **
        F)
      (revInv acctBase krevBase acctBytes contentOff klen F (i + 1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun h hq => ?_) hc5
    rw [sepConj_emp_left'] at hq
    unfold revInv
    have hq1 : (((.x15 : Reg) ↦ᵣ
          ((acctBytes[contentOff + klen - 1 - i]'hidx).zeroExtend 64)) **
        (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
            - BitVec.ofNat 64 (i + 1))) **
          ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 (i + 1))) **
          ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - (i + 1))) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion acctBase acctBytes **
          bytesRegion krevBase
            (revState ((acctBytes.drop contentOff).take klen) (i + 1)) **
          F)) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x15 _)
      (fun _ hh => hh) h hq1
    xperm_hyp hq2
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (klen - i) = (0 : Word)))
      (PT := ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 i)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x15 : Reg) ↦ᵣ v15) **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) i) **
        F)
      (PF := ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 i)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x15 : Reg) ↦ᵣ v15) **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) i) **
        F)
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hc => absurd hc (rev_ctr_ne_zero klen i hi hklen))
      (fun _ => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hbody))


/-! ### §4.4  Exhaustion (header BEQ taken at `i = klen`) and the whole loop -/

/-- Exhaustion: at `i = klen` the counter is zero, the header `BEQ` exits to
    the post-loop station (`base + 248`) with `keyRev32` of the key content
    materialised in the scratch region. -/
theorem bsre_revExh_spec (base acctBase krevBase : Word)
    (acctBytes : List (BitVec 8)) (contentOff klen : Nat) (F : Assertion)
    (hF : F.pcFree) (hklen : klen ≤ 32)
    (hcw : contentOff + klen ≤ acctBytes.length)
    (hbound : 4 * bsreProg.length < 2 ^ 64) :
    cpsTripleWithin 1 (base + 220) (base + 248)
      (CodeReq.ofProg base bsreProg)
      (revInv acctBase krevBase acctBytes contentOff klen F klen)
      (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 klen)) **
       ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
       ((.x30 : Reg) ↦ᵣ (0 : Word)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x15 **
       bytesRegion acctBase acctBytes **
       bytesRegion krevBase (keyRev32 ((acctBytes.drop contentOff).take klen)) **
       F) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  have hkeylen : ((acctBytes.drop contentOff).take klen).length = klen := by
    simp
    omega
  have hctr0 : (BitVec.ofNat 64 (klen - klen) : Word) = (0 : Word) := by
    rw [Nat.sub_self]
    rfl
  have hfull : revState ((acctBytes.drop contentOff).take klen) klen
      = keyRev32 ((acctBytes.drop contentOff).take klen) := by
    have h := revState_full ((acctBytes.drop contentOff).take klen) (by omega)
    rwa [hkeylen] at h
  unfold revInv
  -- header guard station (taken: counter = 0)
  have hbrHdr := cpsBranchWithin_frameR
    (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
        - BitVec.ofNat 64 klen)) **
      ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
      regOwn .x15 **
      bytesRegion acctBase acctBytes **
      bytesRegion krevBase
        (revState ((acctBytes.drop contentOff).take klen) klen) **
      F)
    (by pcf; exact hF)
    (cpsBranchWithin_extend_code (cr' := CR)
      (h := beq_spec_gen_within .x30 .x0 (28 : BitVec 13)
        (BitVec.ofNat 64 (klen - klen)) (0 : Word) (base + 220))
      (hmono := CodeReq.ofProg_mem_at base (base + 220) bsreProg 55
        (.BEQ .x30 .x0 (28 : BitVec 13))
        rfl (by decide +kernel) (by decide +kernel) hbound))
  rw [show base + 220 + signExtend13 (28 : BitVec 13) = base + 248 from by
        rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide]
        bv_omega,
      show base + 220 + 4 = base + 224 from by bv_omega] at hbrHdr
  -- the taken arm: 0 steps, entail into the stated post
  have hid : cpsTripleWithin 0 (base + 248) (base + 248) CR
      (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 klen)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - klen)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x15 **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) klen) **
        F)
      (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 klen)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - klen)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x15 **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) klen) **
        F) :=
    fun R hR s hcr hPR hpc => ⟨0, Nat.le_refl 0, s, rfl, hpc, hPR⟩
  have htaken := cpsTripleWithin_weaken (fun _ hp => hp)
    (fun h hq => by
      rw [hfull, hctr0] at hq
      exact hq) hid
  refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (retJoinStation_spec
      (cond := (BitVec.ofNat 64 (klen - klen) = (0 : Word)))
      (PT := ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 klen)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - klen)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x15 **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) klen) **
        F)
      (PF := ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 klen)) **
        ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
        ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - klen)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x15 **
        bytesRegion acctBase acctBytes **
        bytesRegion krevBase
          (revState ((acctBytes.drop contentOff).take klen) klen) **
        F)
      hbrHdr
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun _ => htaken)
      (fun hc => absurd hctr0 hc))


/-- **The whole byte-reverse loop** (header entry to post-loop station):
    `klen` iterations then the taken exit, materialising `keyRev32` of the
    key content window in the pre-zeroed scratch. -/
theorem bsre_revLoop_spec (base acctBase krevBase : Word)
    (acctBytes : List (BitVec 8)) (contentOff klen : Nat) (F : Assertion)
    (hF : F.pcFree)
    (halignA : acctBase.toNat % 8 = 0) (halignK : krevBase.toNat % 8 = 0)
    (hcw : contentOff + klen ≤ acctBytes.length) (hklen : klen ≤ 32)
    (hoverA : acctBase.toNat + acctBytes.length ≤ 2 ^ 64)
    (hoverK : krevBase.toNat + 32 ≤ 2 ^ 64)
    (hvalidA : ∀ k, k < acctBytes.length →
      isValidByteAccess (acctBase + BitVec.ofNat 64 k) = true)
    (hvalidK : ∀ k, k < 32 →
      isValidByteAccess (krevBase + BitVec.ofNat 64 k) = true)
    (hbound : 4 * bsreProg.length < 2 ^ 64) :
    cpsTripleWithin (klen * 7 + 1) (base + 220) (base + 248)
      (CodeReq.ofProg base bsreProg)
      (revInv acctBase krevBase acctBytes contentOff klen F 0)
      (((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen) - 1
          - BitVec.ofNat 64 klen)) **
       ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 klen)) **
       ((.x30 : Reg) ↦ᵣ (0 : Word)) **
       ((.x0 : Reg) ↦ᵣ (0 : Word)) **
       regOwn .x15 **
       bytesRegion acctBase acctBytes **
       bytesRegion krevBase (keyRev32 ((acctBytes.drop contentOff).take klen)) **
       F) :=
  retLoop_spec klen 7 1
    (revInv acctBase krevBase acctBytes contentOff klen F)
    (fun i hi => bsre_revIter_spec base acctBase krevBase acctBytes
      contentOff klen F hF halignA halignK hcw hklen hoverA hoverK
      hvalidA hvalidK hbound i hi)
    (bsre_revExh_spec base acctBase krevBase acctBytes contentOff klen F
      hF hklen hcw hbound)


/-! ## §5  The exec-log scan loop (slots 68–95)

    Pointer-descending two-exit scan over the 128-byte log entries: from the
    past-last-entry cursor, step back one entry (slot 68), compare the
    entry's addrHash (4 dwords vs `x8`) then slotKey (4 dwords vs `x31` =
    `bsr_krev`); a full 8/8 match exits FOUND (slot 93's jump to the
    advance join, slot 97); any mismatch falls to the scan-next station
    (slots 94–95), which either loops (entries remain) or exits ABSENT
    (slot 96's jump to the reject stub).  Folds with
    `twoExitRetLoopBottom_spec` (`N = count - 1` full rounds; ABSENT can
    only fire in the last round, via the `bne x28, x9` fall-through). -/

end BalStorageReadsExecLogSpec
end EvmAsm.Codegen
