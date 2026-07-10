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
     9–14   mv s0,a0 ; mv s1,a3 ; mv s2,a4 ; mv s6,a1 ; mv a0,a1 ; mv a1,a2
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
    64–65   slli x28,t2,7 ; add x28,s1,x28   (past-last log entry)
    66–67   la x31, bsr_krev
    68      addi x28, x28, -128          (SCAN LOOP HEAD: step to prev entry)
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
#guard bsreProg[68]? = some (.ADDI .x28 .x28 (-128 : BitVec 12))
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

#print axioms bsre_matchTail_spec
#print axioms bsre_rejectTail_spec

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

#print axioms bsre_revIter_spec

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

#print axioms bsre_revExh_spec

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

#print axioms bsre_revLoop_spec

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

/-- Dword slot `k` of log entry `t`: the log region's dword at index
    `16 * t + k` (128-byte entries = 16 dwords). -/
def entryDword (logBytes : List (BitVec 8)) (t k : Nat) : Word :=
  packBytes ((logBytes.drop (8 * (16 * t + k))).take 8)

/-- The 8-dword comparison the cascade implements: addrHash dwords 0–3
    against the addr region, slotKey dwords 4–7 against the krev region.
    (Equivalent to the byte-slice `entryMatches` via
    `bytes_eq_of_dwordSlots_eq` — bridged separately.) -/
def entryMatchesD (logBytes addrBytes key32 : List (BitVec 8)) (t : Nat) : Prop :=
  (∀ k, k < 4 →
    entryDword logBytes t k = packBytes ((addrBytes.drop (8 * k)).take 8)) ∧
  (∀ k, k < 4 →
    entryDword logBytes t (4 + k) = packBytes ((key32.drop (8 * k)).take 8))

/-- Scan invariant at the loop head (slot 68), after `j` entries checked
    (from the log's END): the cursor sits at the past-end boundary of entry
    `count - j - 1`, and no entry with index ≥ count - j matches. -/
def scanInv (logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat)
    (F : Assertion) (j : Nat) : Assertion :=
  ((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (128 * (count - j)))) **
  ((.x8 : Reg) ↦ᵣ addrPtr) **
  ((.x9 : Reg) ↦ᵣ logBase) **
  ((.x31 : Reg) ↦ᵣ krevBase) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x29 ** regOwn .x30 **
  bytesRegion logBase logBytes **
  bytesRegion addrPtr addrBytes **
  bytesRegion krevBase key32 **
  (⌜∀ t, count - j ≤ t → t < count →
      ¬ entryMatchesD logBytes addrBytes key32 t⌝ : Assertion) **
  F

/-- **FOUND exit** (`base + 388`, the advance join at slot 97): some entry
    of the exec log matches; the cursor and compare scratch are released. -/
def scanFound (logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat)
    (F : Assertion) : Assertion :=
  regOwn .x28 **
  ((.x8 : Reg) ↦ᵣ addrPtr) **
  ((.x9 : Reg) ↦ᵣ logBase) **
  ((.x31 : Reg) ↦ᵣ krevBase) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x29 ** regOwn .x30 **
  bytesRegion logBase logBytes **
  bytesRegion addrPtr addrBytes **
  bytesRegion krevBase key32 **
  (⌜∃ t, t < count ∧ entryMatchesD logBytes addrBytes key32 t⌝ : Assertion) **
  F

/-- **ABSENT exit** (`base + 400`, the reject stub at slot 100): the whole
    log has been scanned and no entry matches. -/
def scanAbsent (logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat)
    (F : Assertion) : Assertion :=
  regOwn .x28 **
  ((.x8 : Reg) ↦ᵣ addrPtr) **
  ((.x9 : Reg) ↦ᵣ logBase) **
  ((.x31 : Reg) ↦ᵣ krevBase) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x29 ** regOwn .x30 **
  bytesRegion logBase logBytes **
  bytesRegion addrPtr addrBytes **
  bytesRegion krevBase key32 **
  (⌜∀ t, t < count → ¬ entryMatchesD logBytes addrBytes key32 t⌝ : Assertion) **
  F

/-! ### §5.1  Round-state shape, address/counter bridges -/

/-- The register/region state inside a scan round (between the head `ADDI`
    and the scan-next station): the cursor pinned at entry `t`
    (`8 * (16 * t)` is the `ld_cursor` dword-slot form of `128 * t`), the
    compare scratch holding arbitrary values. -/
private def scanRegs (logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (t : Nat) (F : Assertion)
    (v29 v30 : Word) : Assertion :=
  ((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
  ((.x8 : Reg) ↦ᵣ addrPtr) **
  ((.x9 : Reg) ↦ᵣ logBase) **
  ((.x31 : Reg) ↦ᵣ krevBase) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  ((.x29 : Reg) ↦ᵣ v29) **
  ((.x30 : Reg) ↦ᵣ v30) **
  bytesRegion logBase logBytes **
  bytesRegion addrPtr addrBytes **
  bytesRegion krevBase key32 **
  F

/-- The head `ADDI x28, x28, -128` steps the past-end cursor of entry
    `count - j` down to the base of entry `count - j - 1`. -/
private theorem scan_cursor_step (logBase : Word) (count j : Nat)
    (hj : j < count) (_hcnt : 128 * count < 2 ^ 64) :
    logBase + BitVec.ofNat 64 (128 * (count - j)) + signExtend12 (-128 : BitVec 12)
      = logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))) := by
  rw [show signExtend12 (-128 : BitVec 12) = (-128 : Word) from by decide]
  bv_omega

/-- While entries remain (`1 ≤ T`), the stepped cursor differs from the log
    base — no wraparound thanks to the log-size bound. -/
private theorem scan_cursor_ne (logBase : Word) (T : Nat)
    (h1 : 1 ≤ T) (h2 : 128 * T < 2 ^ 64) :
    logBase + BitVec.ofNat 64 (8 * (16 * T)) ≠ logBase := by
  bv_omega

/-- At the first entry (`T = 0`) the stepped cursor IS the log base. -/
private theorem scan_cursor_eq_zero (logBase : Word) :
    logBase + BitVec.ofNat 64 (8 * (16 * 0)) = logBase := by
  bv_omega

/-! ### §5.2  One compare station (generic) and the station merge -/

/-- One compare station
    `LD x29, 8qL(x28) ; LD x30, 8qT(rt) ; BNE x29, x30, boff`
    — generic in the station address, the entry-dword index `qL`, the
    target register/region (`rt`/`tgtBytes`) and dword index `qT`, and the
    branch offset.  Loads entry dword `qL` (through the round cursor) and
    target dword `qT`, then branches on disequality; `G` carries the
    untouched ambient state. -/
private theorem bsre_stationBr_spec {CR : CodeReq} (A : Word) (boff : BitVec 13)
    (logBase tgtBase : Word) (logBytes tgtBytes : List (BitVec 8))
    (rt : Reg) (t qL qT : Nat) (v29 v30 : Word)
    (G : Assertion) (hG : G.pcFree)
    (hqL : 8 * (16 * t + qL) < logBytes.length)
    (hqT : 8 * qT < tgtBytes.length)
    (himmL : 8 * qL < 2 ^ 11) (himmT : 8 * qT < 2 ^ 11)
    (hmem1 : ∀ a i,
      CodeReq.singleton A (.LD .x29 .x28 (BitVec.ofNat 12 (8 * qL))) a = some i →
      CR a = some i)
    (hmem2 : ∀ a i,
      CodeReq.singleton (A + 4) (.LD .x30 rt (BitVec.ofNat 12 (8 * qT))) a = some i →
      CR a = some i)
    (hmem3 : ∀ a i,
      CodeReq.singleton (A + 8) (.BNE .x29 .x30 boff) a = some i →
      CR a = some i) :
    cpsBranchWithin 3 A CR
      (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
        (rt ↦ᵣ tgtBase) ** ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion tgtBase tgtBytes ** G)
      (A + 8 + signExtend13 boff)
      ((⌜packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)
          ≠ packBytes ((tgtBytes.drop (8 * qT)).take 8)⌝ : Assertion) **
        ((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
        (rt ↦ᵣ tgtBase) **
        ((.x29 : Reg) ↦ᵣ packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)) **
        ((.x30 : Reg) ↦ᵣ packBytes ((tgtBytes.drop (8 * qT)).take 8)) **
        bytesRegion logBase logBytes ** bytesRegion tgtBase tgtBytes ** G)
      (A + 12)
      ((⌜packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)
          = packBytes ((tgtBytes.drop (8 * qT)).take 8)⌝ : Assertion) **
        ((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
        (rt ↦ᵣ tgtBase) **
        ((.x29 : Reg) ↦ᵣ packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)) **
        ((.x30 : Reg) ↦ᵣ packBytes ((tgtBytes.drop (8 * qT)).take 8)) **
        bytesRegion logBase logBytes ** bytesRegion tgtBase tgtBytes ** G) := by
  have hld1 := liftCode (cr' := CR)
    (bytesRegion_ld_cursor_imm_within .x29 .x28 logBase v29 A logBytes (16 * t) qL
      (by decide) hqL himmL) hmem1
  have hld2 := liftCode (cr' := CR)
    (bytesRegion_ld_within .x30 rt tgtBase v30 (A + 4) tgtBytes qT
      (by decide) hqT himmT) hmem2
  rw [show A + 4 + 4 = A + 8 from by bv_omega] at hld2
  have hbne := cpsBranchWithin_extend_code (cr' := CR)
    (h := bne_spec_gen_within .x29 .x30 boff
      (packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8))
      (packBytes ((tgtBytes.drop (8 * qT)).take 8)) (A + 8))
    (hmono := hmem3)
  have hld1F := cpsTripleWithin_frameR
    ((rt ↦ᵣ tgtBase) ** ((.x30 : Reg) ↦ᵣ v30) ** bytesRegion tgtBase tgtBytes ** G)
    (by pcf; exact hG) hld1
  have hld2F := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
      ((.x29 : Reg) ↦ᵣ packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)) **
      bytesRegion logBase logBytes ** G)
    (by pcf; exact hG) hld2
  have hbneF := cpsBranchWithin_frameR
    (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
      (rt ↦ᵣ tgtBase) **
      bytesRegion logBase logBytes ** bytesRegion tgtBase tgtBytes ** G)
    (by pcf; exact hG) hbne
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hld1F hld2F
  have hcomp := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hseq hbneF
  rw [show A + 8 + 4 = A + 12 from by bv_omega] at hcomp
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hcomp
  · exact fun h hp => by xperm_hyp hp
  · exact fun h hq => by xperm_hyp hq
  · exact fun h hq => by xperm_hyp hq

#print axioms bsre_stationBr_spec

/-- `breakStation_spec` instantiated at the station lemma's exact post
    shapes: the taken (mismatch) arm runs a return-tail triple, the
    fall-through (equal) arm continues the cascade with the equality in
    hand. -/
private theorem bsre_stationMerge {n m : Nat} {A tgtT tgtF ret hdr : Word}
    {CR : CodeReq} {P C : Assertion} {a b : Word} {Q I : Assertion}
    (hbr : cpsBranchWithin n A CR P
      tgtT ((⌜a ≠ b⌝ : Assertion) ** C) tgtF ((⌜a = b⌝ : Assertion) ** C))
    (hbreak : a ≠ b → cpsTripleWithin m tgtT ret CR C Q)
    (hfall : a = b → cpsBranchWithin m tgtF CR C ret Q hdr I) :
    cpsBranchWithin (n + m) A CR P ret Q hdr I :=
  breakStation_spec (cond := a ≠ b) hbr (fun _ hq => hq)
    (fun h hq => by
      have h2 := (sepConj_pure_left h).mp hq
      exact (sepConj_pure_left h).mpr ⟨fun hne => hne h2.1, h2.2⟩)
    hbreak
    (fun hnc => hfall (Classical.byContradiction fun hne => hnc hne))

/-! ### §5.3  The scan-next station (slots 94–96) -/

/-- Scan-next, entries remaining (`j + 1 < count`): `MV x29, x9`, then the
    `BNE x28, x29` back-edge is TAKEN (the cursor has not reached the log
    base — no wraparound by the log-size bound), re-establishing the
    invariant at `j + 1` with the freshly refuted entry recorded. -/
private theorem bsre_scanNextIter_spec (base logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat) (F : Assertion)
    (hF : F.pcFree) (hcnt : 128 * count < 2 ^ 64)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (j : Nat) (hj : j + 1 < count)
    (hprev : ∀ t', count - j ≤ t' → t' < count →
      ¬ entryMatchesD logBytes addrBytes key32 t')
    (hnm : ¬ entryMatchesD logBytes addrBytes key32 (count - j - 1))
    (v29 v30 : Word) :
    cpsTripleWithin 3 (base + 376) (base + 272) (CodeReq.ofProg base bsreProg)
      (scanRegs logBase addrPtr krevBase logBytes addrBytes key32
        (count - j - 1) F v29 v30)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F (j + 1)) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  -- MV x29, x9
  have hmv := liftCode (cr' := CR)
    (mv_spec_gen_within .x29 .x9 logBase v29 (base + 376) (by decide))
    (CodeReq.ofProg_mem_at base (base + 376) bsreProg 94 (.MV .x29 .x9)
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 376 + 4 = base + 380 from by bv_omega] at hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
      ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x31 : Reg) ↦ᵣ krevBase) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
      bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
      bytesRegion krevBase key32 ** F)
    (by pcf; exact hF) hmv
  -- BNE x28, x29, -108 — the back-edge
  have hbne := cpsBranchWithin_extend_code (cr' := CR)
    (h := bne_spec_gen_within .x28 .x29 (-108 : BitVec 13)
      (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1)))) logBase (base + 380))
    (hmono := CodeReq.ofProg_mem_at base (base + 380) bsreProg 95
      (.BNE .x28 .x29 (-108 : BitVec 13))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 380 + signExtend13 (-108 : BitVec 13) = base + 272 from by
        rw [show signExtend13 (-108 : BitVec 13) = (-108 : Word) from by decide]
        bv_omega,
      show base + 380 + 4 = base + 384 from by bv_omega] at hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
      ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x30 : Reg) ↦ᵣ v30) **
      bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
      bytesRegion krevBase key32 ** F)
    (by pcf; exact hF) hbne
  -- taken arm entails the invariant at j + 1
  have hent : ∀ h,
      ((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F) : Assertion) h →
      scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F (j + 1) h := by
    intro h hp
    unfold scanInv
    have hpure : ∀ t', count - (j + 1) ≤ t' → t' < count →
        ¬ entryMatchesD logBytes addrBytes key32 t' := by
      intro t' h1 h2
      by_cases he : t' = count - j - 1
      · exact he ▸ hnm
      · exact hprev t' (by omega) h2
    rw [show (128 : Nat) * (count - (j + 1)) = 8 * (16 * (count - j - 1)) from by omega]
    have hp1 : ((((.x29 : Reg) ↦ᵣ logBase) **
        (((.x30 : Reg) ↦ᵣ v30) **
          (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
            ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
            ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
            bytesRegion krevBase key32 ** F))) : Assertion) h := by
      xperm_hyp hp
    have hp2 := sepConj_mono (regIs_to_regOwn .x29 _)
      (sepConj_mono (regIs_to_regOwn .x30 _) (fun _ hh => hh)) h hp1
    have hp3 := (sepConj_pure_left h).mpr ⟨hpure, hp2⟩
    xperm_hyp hp3
  have hident : cpsTripleWithin 0 (base + 272) (base + 272) CR
      ((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F) : Assertion)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F (j + 1)) := by
    refine cpsTripleWithin_weaken (fun _ hp => hp) hent ?_
    exact fun R hR s hcr hPR hpc => ⟨0, Nat.le_refl 0, s, rfl, hpc, hPR⟩
  have hstation := retJoinStation_spec (m := 1)
    (cond := (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))) ≠ logBase))
    (PT := (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F))
    (PF := (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F))
    hbneF
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : ((⌜logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1)))
            = logBase⌝ : Assertion) **
          (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * (count - j - 1))))) **
            ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
            ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
            bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
            bytesRegion krevBase key32 ** F)) h := by
        xperm_hyp hq
      have h2 := (sepConj_pure_left h).mp hq1
      exact (sepConj_pure_left h).mpr ⟨fun hne => hne h2.1, h2.2⟩)
    (fun _ => cpsTripleWithin_mono_nSteps (by omega) hident)
    (fun hnc => absurd
      (scan_cursor_ne logBase (count - j - 1) (by omega) (by omega)) hnc)
  refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hstation)
  exact fun h hp => by unfold scanRegs at hp; xperm_hyp hp

#print axioms bsre_scanNextIter_spec

/-- Scan-next, last round (`j + 1 = count`, cursor at the log base): the
    `BNE x28, x29` back-edge FALLS THROUGH and slot 96's `JAL` exits to the
    reject stub — the whole log has been scanned, the slot is absent. -/
private theorem bsre_scanNextLast_spec (base logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat) (F : Assertion)
    (hF : F.pcFree)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (j : Nat) (hj : j + 1 = count)
    (hprev : ∀ t', count - j ≤ t' → t' < count →
      ¬ entryMatchesD logBytes addrBytes key32 t')
    (hnm : ¬ entryMatchesD logBytes addrBytes key32 (count - j - 1))
    (v29 v30 : Word) :
    cpsTripleWithin 3 (base + 376) (base + 400) (CodeReq.ofProg base bsreProg)
      (scanRegs logBase addrPtr krevBase logBytes addrBytes key32
        (count - j - 1) F v29 v30)
      (scanAbsent logBase addrPtr krevBase logBytes addrBytes key32 count F) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  rw [show count - j - 1 = 0 from by omega]
  have hnm0 : ¬ entryMatchesD logBytes addrBytes key32 0 := by
    rw [show (0 : Nat) = count - j - 1 from by omega]
    exact hnm
  -- MV x29, x9
  have hmv := liftCode (cr' := CR)
    (mv_spec_gen_within .x29 .x9 logBase v29 (base + 376) (by decide))
    (CodeReq.ofProg_mem_at base (base + 376) bsreProg 94 (.MV .x29 .x9)
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 376 + 4 = base + 380 from by bv_omega] at hmv
  have hmvF := cpsTripleWithin_frameR
    (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
      ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x31 : Reg) ↦ᵣ krevBase) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
      bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
      bytesRegion krevBase key32 ** F)
    (by pcf; exact hF) hmv
  -- BNE x28, x29, -108 — falls through (cursor = log base)
  have hbne := cpsBranchWithin_extend_code (cr' := CR)
    (h := bne_spec_gen_within .x28 .x29 (-108 : BitVec 13)
      (logBase + BitVec.ofNat 64 (8 * (16 * 0))) logBase (base + 380))
    (hmono := CodeReq.ofProg_mem_at base (base + 380) bsreProg 95
      (.BNE .x28 .x29 (-108 : BitVec 13))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 380 + signExtend13 (-108 : BitVec 13) = base + 272 from by
        rw [show signExtend13 (-108 : BitVec 13) = (-108 : Word) from by decide]
        bv_omega,
      show base + 380 + 4 = base + 384 from by bv_omega] at hbne
  have hbneF := cpsBranchWithin_frameR
    (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
      ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x30 : Reg) ↦ᵣ v30) **
      bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
      bytesRegion krevBase key32 ** F)
    (by pcf; exact hF) hbne
  -- the fall-through JAL to the reject stub, entailing the ABSENT post
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (16 : BitVec 21) (base + 384))
    (CodeReq.ofProg_mem_at base (base + 384) bsreProg 96 (.JAL .x0 (16 : BitVec 21))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 384 + signExtend21 (16 : BitVec 21) = base + 400 from by
    rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]
    bv_omega] at hjal
  have hjalF := cpsTripleWithin_frameR
    ((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F) : Assertion)
    (by pcf; exact hF) hjal
  have hpure : ∀ t', t' < count → ¬ entryMatchesD logBytes addrBytes key32 t' := by
    intro t' h2
    by_cases he : t' = 0
    · exact he ▸ hnm0
    · exact hprev t' (by omega) h2
  have hfall : cpsTripleWithin 1 (base + 384) (base + 400) CR
      ((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F) : Assertion)
      (scanAbsent logBase addrPtr krevBase logBytes addrBytes key32 count F) := by
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [sepConj_emp_left']; exact hp) (fun h hq => ?_) hjalF
    rw [sepConj_emp_left'] at hq
    unfold scanAbsent
    have hq1 : ((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
        (((.x29 : Reg) ↦ᵣ logBase) **
          (((.x30 : Reg) ↦ᵣ v30) **
            (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
              ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
              bytesRegion krevBase key32 ** F)))) : Assertion) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (sepConj_mono (regIs_to_regOwn .x30 _) (fun _ hh => hh))) h hq1
    have hq3 := (sepConj_pure_left h).mpr ⟨hpure, hq2⟩
    xperm_hyp hq3
  have hstation := retJoinStation_spec (m := 1)
    (cond := (logBase + BitVec.ofNat 64 (8 * (16 * 0)) ≠ logBase))
    (PT := (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F))
    (PF := (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
        ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
        ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F))
    hbneF
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : ((⌜logBase + BitVec.ofNat 64 (8 * (16 * 0)) = logBase⌝ : Assertion) **
          (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * 0)))) **
            ((.x29 : Reg) ↦ᵣ logBase) ** ((.x8 : Reg) ↦ᵣ addrPtr) **
            ((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
            ((.x0 : Reg) ↦ᵣ (0 : Word)) ** ((.x30 : Reg) ↦ᵣ v30) **
            bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
            bytesRegion krevBase key32 ** F)) h := by
        xperm_hyp hq
      have h2 := (sepConj_pure_left h).mp hq1
      exact (sepConj_pure_left h).mpr ⟨fun hne => hne h2.1, h2.2⟩)
    (fun hc => absurd (scan_cursor_eq_zero logBase) hc)
    (fun _ => hfall)
  refine cpsTripleWithin_weaken ?_ (fun _ hq => hq)
    (cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hmvF hstation)
  exact fun h hp => by unfold scanRegs at hp; xperm_hyp hp

#print axioms bsre_scanNextLast_spec

/-! ### §5.4  The 8-station compare cascade (slots 69–93) -/

/-- Address-half compare station (dwords 0–3, target register `x8`), with
    pre/post in canonical `scanRegs` order. -/
private theorem bsre_stationA_spec {CR : CodeReq}
    (logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (A : Word) (boff : BitVec 13) (t q : Nat) (v29 v30 : Word)
    (hqL : 8 * (16 * t + q) < logBytes.length)
    (hqT : 8 * q < addrBytes.length) (himm : 8 * q < 2 ^ 11)
    (hmem1 : ∀ a i,
      CodeReq.singleton A (.LD .x29 .x28 (BitVec.ofNat 12 (8 * q))) a = some i →
      CR a = some i)
    (hmem2 : ∀ a i,
      CodeReq.singleton (A + 4) (.LD .x30 .x8 (BitVec.ofNat 12 (8 * q))) a = some i →
      CR a = some i)
    (hmem3 : ∀ a i,
      CodeReq.singleton (A + 8) (.BNE .x29 .x30 boff) a = some i →
      CR a = some i) :
    cpsBranchWithin 3 A CR
      (scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F v29 v30)
      (A + 8 + signExtend13 boff)
      ((⌜packBytes ((logBytes.drop (8 * (16 * t + q))).take 8)
          ≠ packBytes ((addrBytes.drop (8 * q)).take 8)⌝ : Assertion) **
        scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F
          (packBytes ((logBytes.drop (8 * (16 * t + q))).take 8))
          (packBytes ((addrBytes.drop (8 * q)).take 8)))
      (A + 12)
      ((⌜packBytes ((logBytes.drop (8 * (16 * t + q))).take 8)
          = packBytes ((addrBytes.drop (8 * q)).take 8)⌝ : Assertion) **
        scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F
          (packBytes ((logBytes.drop (8 * (16 * t + q))).take 8))
          (packBytes ((addrBytes.drop (8 * q)).take 8))) := by
  have hst := bsre_stationBr_spec (CR := CR) A boff logBase addrPtr
    logBytes addrBytes .x8 t q q v29 v30
    (((.x9 : Reg) ↦ᵣ logBase) ** ((.x31 : Reg) ↦ᵣ krevBase) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion krevBase key32 ** F)
    (by pcf; exact hF) hqL hqT himm himm hmem1 hmem2 hmem3
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hst
  · exact fun h hp => by unfold scanRegs at hp; xperm_hyp hp
  · exact fun h hq => by unfold scanRegs; xperm_hyp hq
  · exact fun h hq => by unfold scanRegs; xperm_hyp hq

/-- Key-half compare station (dwords 4–7, target register `x31`), with
    pre/post in canonical `scanRegs` order. -/
private theorem bsre_stationK_spec {CR : CodeReq}
    (logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (F : Assertion) (hF : F.pcFree)
    (A : Word) (boff : BitVec 13) (t qL qT : Nat) (v29 v30 : Word)
    (hqL : 8 * (16 * t + qL) < logBytes.length)
    (hqT : 8 * qT < key32.length)
    (himmL : 8 * qL < 2 ^ 11) (himmT : 8 * qT < 2 ^ 11)
    (hmem1 : ∀ a i,
      CodeReq.singleton A (.LD .x29 .x28 (BitVec.ofNat 12 (8 * qL))) a = some i →
      CR a = some i)
    (hmem2 : ∀ a i,
      CodeReq.singleton (A + 4) (.LD .x30 .x31 (BitVec.ofNat 12 (8 * qT))) a = some i →
      CR a = some i)
    (hmem3 : ∀ a i,
      CodeReq.singleton (A + 8) (.BNE .x29 .x30 boff) a = some i →
      CR a = some i) :
    cpsBranchWithin 3 A CR
      (scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F v29 v30)
      (A + 8 + signExtend13 boff)
      ((⌜packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)
          ≠ packBytes ((key32.drop (8 * qT)).take 8)⌝ : Assertion) **
        scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F
          (packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8))
          (packBytes ((key32.drop (8 * qT)).take 8)))
      (A + 12)
      ((⌜packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8)
          = packBytes ((key32.drop (8 * qT)).take 8)⌝ : Assertion) **
        scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F
          (packBytes ((logBytes.drop (8 * (16 * t + qL))).take 8))
          (packBytes ((key32.drop (8 * qT)).take 8))) := by
  have hst := bsre_stationBr_spec (CR := CR) A boff logBase krevBase
    logBytes key32 .x31 t qL qT v29 v30
    (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bytesRegion addrPtr addrBytes ** F)
    (by pcf; exact hF) hqL hqT himmL himmT hmem1 hmem2 hmem3
  refine cpsBranchWithin_weaken ?_ ?_ ?_ hst
  · exact fun h hp => by unfold scanRegs at hp; xperm_hyp hp
  · exact fun h hq => by unfold scanRegs; xperm_hyp hq
  · exact fun h hq => by unfold scanRegs; xperm_hyp hq

#print axioms bsre_stationA_spec
#print axioms bsre_stationK_spec

/-- **The compare cascade** from the first station (`base + 276`, slot 69),
    generic in the scan-next continuation `hnext` (invoked at `base + 376`
    with the refuted entry in hand): every mismatch arm runs `hnext`; the
    8/8-match path exits at `base + 388` (slot 93's `JAL`, the advance
    join) with the FOUND post. -/
private theorem bsre_cascade_spec (base logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat) (F : Assertion)
    (hF : F.pcFree) (hlog : logBytes.length = 128 * count)
    (haddr : addrBytes.length = 32) (hkey : key32.length = 32)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (t : Nat) (ht : t < count) (v29 v30 : Word)
    (ret : Word) (Q : Assertion)
    (hnext : ∀ v29' v30', ¬ entryMatchesD logBytes addrBytes key32 t →
      cpsTripleWithin 3 (base + 376) ret (CodeReq.ofProg base bsreProg)
        (scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F v29' v30')
        Q) :
    cpsBranchWithin 27 (base + 276) (CodeReq.ofProg base bsreProg)
      (scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F v29 v30)
      ret Q
      (base + 388)
      (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  have hlen : ∀ k : Nat, k < 8 → 8 * (16 * t + k) < logBytes.length := by
    intro k hk
    rw [hlog]
    omega
  -- the eight station branch specs
  have hst1 := bsre_stationA_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 276) (92 : BitVec 13) t 0 v29 v30
    (hlen 0 (by omega)) (by rw [haddr]; omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 276) bsreProg 69
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 0)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 276 + 4) bsreProg 70
      (.LD .x30 .x8 (BitVec.ofNat 12 (8 * 0)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 276 + 8) bsreProg 71
      (.BNE .x29 .x30 (92 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 276 + 8 + signExtend13 (92 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (92 : BitVec 13) = (92 : Word) from by decide]
        bv_omega,
      show base + 276 + 12 = base + 288 from by bv_omega] at hst1
  have hst2 := bsre_stationA_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 288) (80 : BitVec 13) t 1
    (packBytes ((logBytes.drop (8 * (16 * t + 0))).take 8))
    (packBytes ((addrBytes.drop (8 * 0)).take 8))
    (hlen 1 (by omega)) (by rw [haddr]; omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 288) bsreProg 72
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 1)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 288 + 4) bsreProg 73
      (.LD .x30 .x8 (BitVec.ofNat 12 (8 * 1)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 288 + 8) bsreProg 74
      (.BNE .x29 .x30 (80 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 288 + 8 + signExtend13 (80 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (80 : BitVec 13) = (80 : Word) from by decide]
        bv_omega,
      show base + 288 + 12 = base + 300 from by bv_omega] at hst2
  have hst3 := bsre_stationA_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 300) (68 : BitVec 13) t 2
    (packBytes ((logBytes.drop (8 * (16 * t + 1))).take 8))
    (packBytes ((addrBytes.drop (8 * 1)).take 8))
    (hlen 2 (by omega)) (by rw [haddr]; omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 300) bsreProg 75
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 2)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 300 + 4) bsreProg 76
      (.LD .x30 .x8 (BitVec.ofNat 12 (8 * 2)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 300 + 8) bsreProg 77
      (.BNE .x29 .x30 (68 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 300 + 8 + signExtend13 (68 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (68 : BitVec 13) = (68 : Word) from by decide]
        bv_omega,
      show base + 300 + 12 = base + 312 from by bv_omega] at hst3
  have hst4 := bsre_stationA_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 312) (56 : BitVec 13) t 3
    (packBytes ((logBytes.drop (8 * (16 * t + 2))).take 8))
    (packBytes ((addrBytes.drop (8 * 2)).take 8))
    (hlen 3 (by omega)) (by rw [haddr]; omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 312) bsreProg 78
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 3)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 312 + 4) bsreProg 79
      (.LD .x30 .x8 (BitVec.ofNat 12 (8 * 3)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 312 + 8) bsreProg 80
      (.BNE .x29 .x30 (56 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 312 + 8 + signExtend13 (56 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (56 : BitVec 13) = (56 : Word) from by decide]
        bv_omega,
      show base + 312 + 12 = base + 324 from by bv_omega] at hst4
  have hst5 := bsre_stationK_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 324) (44 : BitVec 13) t 4 0
    (packBytes ((logBytes.drop (8 * (16 * t + 3))).take 8))
    (packBytes ((addrBytes.drop (8 * 3)).take 8))
    (hlen 4 (by omega)) (by rw [hkey]; omega) (by omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 324) bsreProg 81
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 4)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 324 + 4) bsreProg 82
      (.LD .x30 .x31 (BitVec.ofNat 12 (8 * 0)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 324 + 8) bsreProg 83
      (.BNE .x29 .x30 (44 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 324 + 8 + signExtend13 (44 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (44 : BitVec 13) = (44 : Word) from by decide]
        bv_omega,
      show base + 324 + 12 = base + 336 from by bv_omega] at hst5
  have hst6 := bsre_stationK_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 336) (32 : BitVec 13) t 5 1
    (packBytes ((logBytes.drop (8 * (16 * t + 4))).take 8))
    (packBytes ((key32.drop (8 * 0)).take 8))
    (hlen 5 (by omega)) (by rw [hkey]; omega) (by omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 336) bsreProg 84
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 5)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 336 + 4) bsreProg 85
      (.LD .x30 .x31 (BitVec.ofNat 12 (8 * 1)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 336 + 8) bsreProg 86
      (.BNE .x29 .x30 (32 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 336 + 8 + signExtend13 (32 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (32 : BitVec 13) = (32 : Word) from by decide]
        bv_omega,
      show base + 336 + 12 = base + 348 from by bv_omega] at hst6
  have hst7 := bsre_stationK_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 348) (20 : BitVec 13) t 6 2
    (packBytes ((logBytes.drop (8 * (16 * t + 5))).take 8))
    (packBytes ((key32.drop (8 * 1)).take 8))
    (hlen 6 (by omega)) (by rw [hkey]; omega) (by omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 348) bsreProg 87
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 6)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 348 + 4) bsreProg 88
      (.LD .x30 .x31 (BitVec.ofNat 12 (8 * 2)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 348 + 8) bsreProg 89
      (.BNE .x29 .x30 (20 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 348 + 8 + signExtend13 (20 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (20 : BitVec 13) = (20 : Word) from by decide]
        bv_omega,
      show base + 348 + 12 = base + 360 from by bv_omega] at hst7
  have hst8 := bsre_stationK_spec (CR := CR) logBase addrPtr krevBase
    logBytes addrBytes key32 F hF (base + 360) (8 : BitVec 13) t 7 3
    (packBytes ((logBytes.drop (8 * (16 * t + 6))).take 8))
    (packBytes ((key32.drop (8 * 2)).take 8))
    (hlen 7 (by omega)) (by rw [hkey]; omega) (by omega) (by omega)
    (CodeReq.ofProg_mem_at base (base + 360) bsreProg 90
      (.LD .x29 .x28 (BitVec.ofNat 12 (8 * 7)))
      rfl (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 360 + 4) bsreProg 91
      (.LD .x30 .x31 (BitVec.ofNat 12 (8 * 3)))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
    (CodeReq.ofProg_mem_at base (base + 360 + 8) bsreProg 92
      (.BNE .x29 .x30 (8 : BitVec 13))
      (by bv_omega) (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 360 + 8 + signExtend13 (8 : BitVec 13) = base + 376 from by
        rw [show signExtend13 (8 : BitVec 13) = (8 : Word) from by decide]
        bv_omega,
      show base + 360 + 12 = base + 372 from by bv_omega] at hst8
  -- the merge chain: every mismatch arm runs `hnext`, equalities accumulate
  refine bsre_stationMerge (m := 24) hst1 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.1 0 (by omega))))
  intro heq0
  refine bsre_stationMerge (m := 21) hst2 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.1 1 (by omega))))
  intro heq1
  refine bsre_stationMerge (m := 18) hst3 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.1 2 (by omega))))
  intro heq2
  refine bsre_stationMerge (m := 15) hst4 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.1 3 (by omega))))
  intro heq3
  refine bsre_stationMerge (m := 12) hst5 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.2 0 (by omega))))
  intro heq4
  refine bsre_stationMerge (m := 9) hst6 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.2 1 (by omega))))
  intro heq5
  refine bsre_stationMerge (m := 6) hst7 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.2 2 (by omega))))
  intro heq6
  refine bsre_stationMerge (m := 3) hst8 ?_ ?_
  · exact fun hne => cpsTripleWithin_mono_nSteps (by omega)
      (hnext _ _ (fun hm => hne (hm.2 3 (by omega))))
  intro heq7
  -- all 8 dwords matched: slot 93's JAL to the advance join, FOUND
  have hmatch : entryMatchesD logBytes addrBytes key32 t := by
    constructor
    · intro k hk
      match k, hk with
      | 0, _ => exact heq0
      | 1, _ => exact heq1
      | 2, _ => exact heq2
      | 3, _ => exact heq3
      | (n + 4), hk => exact absurd hk (by omega)
    · intro k hk
      match k, hk with
      | 0, _ => exact heq4
      | 1, _ => exact heq5
      | 2, _ => exact heq6
      | 3, _ => exact heq7
      | (n + 4), hk => exact absurd hk (by omega)
  have hjal := liftCode (cr' := CR)
    (jal_x0_spec_gen_within (16 : BitVec 21) (base + 372))
    (CodeReq.ofProg_mem_at base (base + 372) bsreProg 93 (.JAL .x0 (16 : BitVec 21))
      rfl (by decide +kernel) (by decide +kernel) hbound)
  rw [show base + 372 + signExtend21 (16 : BitVec 21) = base + 388 from by
    rw [show signExtend21 (16 : BitVec 21) = (16 : Word) from by decide]
    bv_omega] at hjal
  have hjalF := cpsTripleWithin_frameR
    (scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F
      (packBytes ((logBytes.drop (8 * (16 * t + 7))).take 8))
      (packBytes ((key32.drop (8 * 3)).take 8)))
    (by unfold scanRegs; pcf; exact hF) hjal
  have hfound : cpsTripleWithin 1 (base + 372) (base + 388) CR
      (scanRegs logBase addrPtr krevBase logBytes addrBytes key32 t F
        (packBytes ((logBytes.drop (8 * (16 * t + 7))).take 8))
        (packBytes ((key32.drop (8 * 3)).take 8)))
      (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F) := by
    refine cpsTripleWithin_weaken
      (fun h hp => by rw [sepConj_emp_left']; exact hp) (fun h hq => ?_) hjalF
    rw [sepConj_emp_left'] at hq
    unfold scanRegs at hq
    unfold scanFound
    have hq1 : ((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (8 * (16 * t)))) **
        (((.x29 : Reg) ↦ᵣ packBytes ((logBytes.drop (8 * (16 * t + 7))).take 8)) **
          (((.x30 : Reg) ↦ᵣ packBytes ((key32.drop (8 * 3)).take 8)) **
            (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
              ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
              bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
              bytesRegion krevBase key32 ** F)))) : Assertion) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x28 _)
      (sepConj_mono (regIs_to_regOwn .x29 _)
        (sepConj_mono (regIs_to_regOwn .x30 _) (fun _ hh => hh))) h hq1
    have hex : ∃ t', t' < count ∧ entryMatchesD logBytes addrBytes key32 t' :=
      ⟨t, ht, hmatch⟩
    have hq3 := (sepConj_pure_left h).mpr ⟨hex, hq2⟩
    xperm_hyp hq3
  exact cpsBranchWithin_mono_nSteps (by omega)
    (cpsTripleWithin_as_cpsBranchWithin_right ret Q hfound)

#print axioms bsre_cascade_spec

/-! ### §5.5  One full round from the loop head, and the whole loop -/

/-- **One scan round, entries remaining** (`j + 1 < count`): from the loop
    head (`base + 272`, slot 68) the round either exits FOUND at
    `base + 388` or loops back to the head with the invariant advanced. -/
theorem bsre_scanIter_spec (base logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat) (F : Assertion)
    (hF : F.pcFree) (hlog : logBytes.length = 128 * count)
    (haddr : addrBytes.length = 32) (hkey : key32.length = 32)
    (hcnt : 128 * count < 2 ^ 64)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (j : Nat) (hj : j + 1 < count) :
    cpsBranchWithin 28 (base + 272) (CodeReq.ofProg base bsreProg)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F j)
      (base + 388)
      (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F)
      (base + 272)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F (j + 1)) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  have hmain : ∀ _hprev : (∀ t', count - j ≤ t' → t' < count →
        ¬ entryMatchesD logBytes addrBytes key32 t'),
      cpsBranchWithin 28 (base + 272) CR
        (((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (128 * (count - j)))) **
            ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
            ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
            bytesRegion krevBase key32 ** F) ** regOwn .x29) ** regOwn .x30)
        (base + 388)
        (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F)
        (base + 272)
        (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F (j + 1)) := by
    intro hprev
    apply cpsBranchWithin_of_forall_regIs_to_regOwn
    intro v30
    refine cpsBranchWithin_weaken ?_ (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x29)
        (P := (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (128 * (count - j)))) **
          ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
          ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
          bytesRegion krevBase key32 ** F) ** ((.x30 : Reg) ↦ᵣ v30))
        (fun v29 => ?_))
    · exact fun h hp => by xperm_hyp hp
    -- the head ADDI steps the cursor to entry `count - j - 1`
    have haddi := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x28
        (logBase + BitVec.ofNat 64 (128 * (count - j))) (-128 : BitVec 12)
        (base + 272) (by decide))
      (CodeReq.ofProg_mem_at base (base + 272) bsreProg 68
        (.ADDI .x28 .x28 (-128 : BitVec 12))
        rfl (by decide +kernel) (by decide +kernel) hbound)
    rw [scan_cursor_step logBase count j (by omega) hcnt,
        show base + 272 + 4 = base + 276 from by bv_omega] at haddi
    have haddiF := cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
        ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F)
      (by pcf; exact hF) haddi
    have hcas := bsre_cascade_spec base logBase addrPtr krevBase logBytes addrBytes
      key32 count F hF hlog haddr hkey hbound (count - j - 1) (by omega) v29 v30
      (base + 272)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F (j + 1))
      (fun v29' v30' hnm => bsre_scanNextIter_spec base logBase addrPtr krevBase
        logBytes addrBytes key32 count F hF hcnt hbound j hj hprev hnm v29' v30')
    have hcomp := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by unfold scanRegs; xperm_hyp hp) haddiF hcas
    refine cpsBranchWithin_weaken ?_ (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_swap hcomp)
    exact fun h hp => by xperm_hyp hp
  refine cpsBranchWithin_weaken ?_ (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_pure_pre hmain)
  exact fun h hp => by unfold scanInv at hp; xperm_hyp hp

#print axioms bsre_scanIter_spec

/-- **The last scan round** (`j + 1 = count`, the cursor about to reach the
    log base): the round either exits FOUND at `base + 388` or falls out to
    the ABSENT exit at `base + 400` with the whole log refuted. -/
theorem bsre_scanLast_spec (base logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat) (F : Assertion)
    (hF : F.pcFree) (hlog : logBytes.length = 128 * count)
    (haddr : addrBytes.length = 32) (hkey : key32.length = 32)
    (hcnt : 128 * count < 2 ^ 64)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (j : Nat) (hj : j + 1 = count) :
    cpsBranchWithin 28 (base + 272) (CodeReq.ofProg base bsreProg)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F j)
      (base + 388)
      (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F)
      (base + 400)
      (scanAbsent logBase addrPtr krevBase logBytes addrBytes key32 count F) := by
  set CR := CodeReq.ofProg base bsreProg with hCR
  have hmain : ∀ _hprev : (∀ t', count - j ≤ t' → t' < count →
        ¬ entryMatchesD logBytes addrBytes key32 t'),
      cpsBranchWithin 28 (base + 272) CR
        (((((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (128 * (count - j)))) **
            ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
            ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
            bytesRegion krevBase key32 ** F) ** regOwn .x29) ** regOwn .x30)
        (base + 388)
        (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F)
        (base + 400)
        (scanAbsent logBase addrPtr krevBase logBytes addrBytes key32 count F) := by
    intro hprev
    apply cpsBranchWithin_of_forall_regIs_to_regOwn
    intro v30
    refine cpsBranchWithin_weaken ?_ (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x29)
        (P := (((.x28 : Reg) ↦ᵣ (logBase + BitVec.ofNat 64 (128 * (count - j)))) **
          ((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
          ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
          bytesRegion krevBase key32 ** F) ** ((.x30 : Reg) ↦ᵣ v30))
        (fun v29 => ?_))
    · exact fun h hp => by xperm_hyp hp
    have haddi := liftCode (cr' := CR)
      (addi_spec_gen_same_within .x28
        (logBase + BitVec.ofNat 64 (128 * (count - j))) (-128 : BitVec 12)
        (base + 272) (by decide))
      (CodeReq.ofProg_mem_at base (base + 272) bsreProg 68
        (.ADDI .x28 .x28 (-128 : BitVec 12))
        rfl (by decide +kernel) (by decide +kernel) hbound)
    rw [scan_cursor_step logBase count j (by omega) hcnt,
        show base + 272 + 4 = base + 276 from by bv_omega] at haddi
    have haddiF := cpsTripleWithin_frameR
      (((.x8 : Reg) ↦ᵣ addrPtr) ** ((.x9 : Reg) ↦ᵣ logBase) **
        ((.x31 : Reg) ↦ᵣ krevBase) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x30 : Reg) ↦ᵣ v30) **
        bytesRegion logBase logBytes ** bytesRegion addrPtr addrBytes **
        bytesRegion krevBase key32 ** F)
      (by pcf; exact hF) haddi
    have hcas := bsre_cascade_spec base logBase addrPtr krevBase logBytes addrBytes
      key32 count F hF hlog haddr hkey hbound (count - j - 1) (by omega) v29 v30
      (base + 400)
      (scanAbsent logBase addrPtr krevBase logBytes addrBytes key32 count F)
      (fun v29' v30' hnm => bsre_scanNextLast_spec base logBase addrPtr krevBase
        logBytes addrBytes key32 count F hF hbound j hj hprev hnm v29' v30')
    have hcomp := cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun h hp => by unfold scanRegs; xperm_hyp hp) haddiF hcas
    refine cpsBranchWithin_weaken ?_ (fun _ hq => hq) (fun _ hq => hq)
      (cpsBranchWithin_swap hcomp)
    exact fun h hp => by xperm_hyp hp
  refine cpsBranchWithin_weaken ?_ (fun _ hq => hq) (fun _ hq => hq)
    (cpsBranchWithin_pure_pre hmain)
  exact fun h hp => by unfold scanInv at hp; xperm_hyp hp

#print axioms bsre_scanLast_spec

/-- **The whole exec-log scan loop** (`count - 1` full rounds then the last
    round): from the loop head with nothing refuted yet, exit FOUND at
    `base + 388` (some entry matches) or ABSENT at `base + 400` (no entry
    matches). -/
theorem bsre_scanLoop_spec (base logBase addrPtr krevBase : Word)
    (logBytes addrBytes key32 : List (BitVec 8)) (count : Nat) (F : Assertion)
    (hF : F.pcFree) (hlog : logBytes.length = 128 * count)
    (haddr : addrBytes.length = 32) (hkey : key32.length = 32)
    (hcnt : 128 * count < 2 ^ 64)
    (hbound : 4 * bsreProg.length < 2 ^ 64)
    (hcount : 0 < count) :
    cpsBranchWithin ((count - 1) * 28 + 28) (base + 272)
      (CodeReq.ofProg base bsreProg)
      (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F 0)
      (base + 388)
      (scanFound logBase addrPtr krevBase logBytes addrBytes key32 count F)
      (base + 400)
      (scanAbsent logBase addrPtr krevBase logBytes addrBytes key32 count F) :=
  twoExitRetLoopBottom_spec (count - 1) 28 28
    (scanInv logBase addrPtr krevBase logBytes addrBytes key32 count F)
    (fun j hjN => bsre_scanIter_spec base logBase addrPtr krevBase logBytes
      addrBytes key32 count F hF hlog haddr hkey hcnt hbound j (by omega))
    (bsre_scanLast_spec base logBase addrPtr krevBase logBytes addrBytes key32
      count F hF hlog haddr hkey hcnt hbound (count - 1) (by omega))

#print axioms bsre_scanLoop_spec

/-! ### §5.6  The dword↔byte-slice bridge (spec-side)

    Connects the 8-dword comparison the cascade implements
    (`entryMatchesD`) to the byte-slice functional spec (`entryMatches`,
    §2) via `bytes_eq_of_dwordSlots_eq`. -/

/-- Dword slot `k` of a 32-byte entry slice IS the corresponding raw log
    dword (pure drop/take index algebra). -/
private theorem dwordSlot_logSlice (logBytes : List (BitVec 8)) (t off k : Nat)
    (hk : 8 * k + 8 ≤ 32) :
    dwordSlot (logSlice logBytes t off 32) k
      = packBytes ((logBytes.drop (128 * t + off + 8 * k)).take 8) := by
  unfold dwordSlot logSlice
  rw [List.drop_take, List.drop_drop, List.take_take]
  rw [show min 8 (32 - 8 * k) = 8 from by omega]

/-- **The bridge**: the cascade's 8-dword comparison is EXACTLY the §2
    byte-slice entry match. -/
theorem entryMatchesD_iff_slices (logBytes addrBytes key32 : List (BitVec 8))
    (t count : Nat) (hlog : logBytes.length = 128 * count) (ht : t < count)
    (haddr : addrBytes.length = 32) (hkey : key32.length = 32) :
    entryMatchesD logBytes addrBytes key32 t
      ↔ entryMatches logBytes t addrBytes key32 := by
  have hslice0 : (logSlice logBytes t 0 32).length = 32 := by
    unfold logSlice
    simp only [List.length_take, List.length_drop, hlog]
    omega
  have hslice32 : (logSlice logBytes t 32 32).length = 32 := by
    unfold logSlice
    simp only [List.length_take, List.length_drop, hlog]
    omega
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · apply bytes_eq_of_dwordSlots_eq 4 _ _ (by rw [hslice0]) (by rw [haddr])
      intro i hi
      rw [dwordSlot_logSlice logBytes t 0 i (by omega)]
      have hd := h1 i hi
      unfold entryDword at hd
      unfold dwordSlot
      rw [show 128 * t + 0 + 8 * i = 8 * (16 * t + i) from by omega]
      exact hd
    · apply bytes_eq_of_dwordSlots_eq 4 _ _ (by rw [hslice32]) (by rw [hkey])
      intro i hi
      rw [dwordSlot_logSlice logBytes t 32 i (by omega)]
      have hd := h2 i hi
      unfold entryDword at hd
      unfold dwordSlot
      rw [show 128 * t + 32 + 8 * i = 8 * (16 * t + (4 + i)) from by omega]
      exact hd
  · intro ⟨h1, h2⟩
    constructor
    · intro k hk
      unfold entryDword
      have hd := dwordSlot_logSlice logBytes t 0 k (by omega)
      rw [h1] at hd
      unfold dwordSlot at hd
      rw [show 8 * (16 * t + k) = 128 * t + 0 + 8 * k from by omega]
      exact hd.symm
    · intro k hk
      unfold entryDword
      have hd := dwordSlot_logSlice logBytes t 32 k (by omega)
      rw [h2] at hd
      unfold dwordSlot at hd
      rw [show 8 * (16 * t + (4 + k)) = 128 * t + 32 + 8 * k from by omega]
      exact hd.symm

#print axioms entryMatchesD_iff_slices

/-! ## §6  Concrete linkage: code requirement, call-site adapters, `la` pairs

    Everything below is at the CONCRETE linked base
    (`GuestAddrs.bal_storage_reads_in_exec_log`) — the walker callees live at
    fixed entries, so the `jal` offsets, code-range disjointness, and `la`
    resolutions are all kernel-decided. -/

/-- Concrete routine/callee entries. -/
abbrev B : Word := (GuestAddrs.bal_storage_reads_in_exec_log : Word)
abbrev WI : Word := (GuestAddrs.rlp_walk_init : Word)
abbrev WN : Word := (GuestAddrs.rlp_walk_next : Word)

/-- The routine's full code requirement: its own bytes plus the two verified
    walker callees at their linked entries. -/
def bsreCR : CodeReq :=
  (CodeReq.ofProg B bsreProg).union
    ((rlp_walk_init_code WI).union (rlp_walk_next_code WN))

/-- The routine's bytes never shadow the walkers (separated code ranges). -/
theorem bsre_prog_disj_walkInit :
    (CodeReq.ofProg B bsreProg).Disjoint (rlp_walk_init_code WI) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bsre_prog_disj_walkNext :
    (CodeReq.ofProg B bsreProg).Disjoint (rlp_walk_next_code WN) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The two walkers occupy separated ranges. -/
theorem bsre_walkInit_disj_walkNext :
    (rlp_walk_init_code WI).Disjoint (rlp_walk_next_code WN) :=
  CodeReq.Disjoint.ofProg_ranges _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Call-site adapter for the `jal rlp_walk_init` at slot 15 (`B + 60`). -/
theorem bsre_callSite15_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 60 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 60 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 60) (B + 60 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 60) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_reads_in_exec_log + 60))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 60) bsreProg 15 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h

#print axioms bsre_callSite15_walk_init

/-- Call-site adapter for the `jal rlp_walk_next` at slot 18 (`B + 72`). -/
theorem bsre_callSite18_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 72 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 72 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 72) (B + 72 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 72) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 72))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 72) bsreProg 18 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h

#print axioms bsre_callSite18_walk_next

/-- Call-site adapter for the `jal rlp_walk_next` at slot 21 (`B + 84`). -/
theorem bsre_callSite21_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 84 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 84 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 84) (B + 84 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 84) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 84))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 84) bsreProg 21 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h

#print axioms bsre_callSite21_walk_next

/-- Call-site adapter for the `jal rlp_walk_next` at slot 24 (`B + 96`). -/
theorem bsre_callSite24_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 96 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 96 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 96) (B + 96 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 96) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 96))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 96) bsreProg 24 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h

#print axioms bsre_callSite24_walk_next

/-- Call-site adapter for the `jal rlp_walk_init` at slot 28 (`B + 112`). -/
theorem bsre_callSite28_walk_init {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WI ((B + 112 + 4) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 112 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 112) (B + 112 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 112) (calleeEntry := WI) (vOld := vRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_init (GuestAddrs.bal_storage_reads_in_exec_log + 112))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 112) bsreProg 28 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkInit
      (fun a i h => CodeReq.union_mono_left a i h) a i h

#print axioms bsre_callSite28_walk_init

/-- Call-site adapter for the `jal rlp_walk_next` at slot 35 (`B + 140`). -/
theorem bsre_callSite35_walk_next {n : Nat} {Prest Q : Assertion} (vRa : Word)
    (hPrest : Prest.pcFree)
    (hcallee : cpsTripleWithin n WN ((B + 140 + 4) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 140 + 4)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 140) (B + 140 + 4) bsreCR
      ((.x1 ↦ᵣ vRa) ** Prest) Q := by
  have hcall := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 140) (calleeEntry := WN) (vOld := vRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (jalOff GuestAddrs.rlp_walk_next (GuestAddrs.bal_storage_reads_in_exec_log + 140))
    (by decide) (by decide) hPrest
    (CodeReq.Disjoint.singleton_ofProg (by decide +kernel))
    hcallee
  refine cpsTripleWithin_extend_code
    (CodeReq.union_split_mono (fun a i h => ?_) (fun a i h => ?_)) hcall
  · exact CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 140) bsreProg 35 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h)
  · exact CodeReq.mono_union_right bsre_prog_disj_walkNext
      (fun a i h => CodeReq.mono_union_right bsre_walkInit_disj_walkNext
        (fun _ _ hh => hh) a i h) a i h

#print axioms bsre_callSite35_walk_next

/-- The `la t0, bsr_krev` pair at slots 45–46: AUIPC+ADDI resolve
    to the linked scratch address. -/
theorem bsre_la_krev1_spec (vOld : Word) :
    cpsTripleWithin 2 (B + 180) (B + 188) bsreCR
      ((.x5 : Reg) ↦ᵣ vOld)
      ((.x5 : Reg) ↦ᵣ (GuestAddrs.bsr_krev : Word)) := by
  have hau := liftCode (cr' := bsreCR)
    (auipc_spec_gen_within .x5 vOld
      (laHi GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 180))
      (B + 180) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 180) bsreProg 45 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 180) + 4 = B + 184 from by decide] at hau
  have haddi := liftCode (cr' := bsreCR)
    (addi_spec_gen_same_within .x5
      ((B + 180) + (((laHi GuestAddrs.bsr_krev
          (GuestAddrs.bal_storage_reads_in_exec_log + 180)).zeroExtend 32
            <<< 12).signExtend 64))
      (laLo GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 180))
      (B + 184) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 184) bsreProg 46 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 184) + 4 = B + 188 from by decide,
      show (B + 180) + (((laHi GuestAddrs.bsr_krev
          (GuestAddrs.bal_storage_reads_in_exec_log + 180)).zeroExtend 32
            <<< 12).signExtend 64)
        + signExtend12 (laLo GuestAddrs.bsr_krev
            (GuestAddrs.bal_storage_reads_in_exec_log + 180))
        = (GuestAddrs.bsr_krev : Word) from by decide] at haddi
  exact cpsTripleWithin_seq_same_cr hau haddi

#print axioms bsre_la_krev1_spec

/-- The `la x31, bsr_krev` pair at slots 66–67: AUIPC+ADDI resolve
    to the linked scratch address. -/
theorem bsre_la_krev2_spec (vOld : Word) :
    cpsTripleWithin 2 (B + 264) (B + 272) bsreCR
      ((.x31 : Reg) ↦ᵣ vOld)
      ((.x31 : Reg) ↦ᵣ (GuestAddrs.bsr_krev : Word)) := by
  have hau := liftCode (cr' := bsreCR)
    (auipc_spec_gen_within .x31 vOld
      (laHi GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 264))
      (B + 264) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 264) bsreProg 66 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 264) + 4 = B + 268 from by decide] at hau
  have haddi := liftCode (cr' := bsreCR)
    (addi_spec_gen_same_within .x31
      ((B + 264) + (((laHi GuestAddrs.bsr_krev
          (GuestAddrs.bal_storage_reads_in_exec_log + 264)).zeroExtend 32
            <<< 12).signExtend 64))
      (laLo GuestAddrs.bsr_krev (GuestAddrs.bal_storage_reads_in_exec_log + 264))
      (B + 268) (by decide))
    (fun a i h => CodeReq.union_mono_left a i
      (CodeReq.ofProg_mem_at B (B + 268) bsreProg 67 _
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) a i h))
  rw [show (B + 268) + 4 = B + 272 from by decide,
      show (B + 264) + (((laHi GuestAddrs.bsr_krev
          (GuestAddrs.bal_storage_reads_in_exec_log + 264)).zeroExtend 32
            <<< 12).signExtend 64)
        + signExtend12 (laLo GuestAddrs.bsr_krev
            (GuestAddrs.bal_storage_reads_in_exec_log + 264))
        = (GuestAddrs.bsr_krev : Word) from by decide] at haddi
  exact cpsTripleWithin_seq_same_cr hau haddi

#print axioms bsre_la_krev2_spec


end BalStorageReadsExecLogSpec

end EvmAsm.Codegen
