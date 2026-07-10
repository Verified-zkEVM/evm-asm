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
    `key` is that content window. -/
def revInv (acctBase krevBase : Word) (acctBytes : List (BitVec 8))
    (contentOff klen : Nat) (F : Assertion) (i : Nat) : Assertion :=
  ((.x28 : Reg) ↦ᵣ (acctBase + BitVec.ofNat 64 (contentOff + klen - 1 - i))) **
  ((.x29 : Reg) ↦ᵣ (krevBase + BitVec.ofNat 64 i)) **
  ((.x30 : Reg) ↦ᵣ BitVec.ofNat 64 (klen - i)) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x15 **
  bytesRegion acctBase acctBytes **
  bytesRegion krevBase
    (revState ((acctBytes.drop contentOff).take klen) i) **
  F

end BalStorageReadsExecLogSpec

end EvmAsm.Codegen
