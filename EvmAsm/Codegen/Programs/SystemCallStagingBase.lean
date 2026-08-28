/-
  EvmAsm.Codegen.Programs.SystemCallStagingBase

  Shared geometry for the `stage_system_call` whole-routine proof (#12206
  item 1): symbolic base, `pc` indexing, the routine's `CodeReq`, the BSS cell
  addresses it owns, and every pc-arithmetic bridge the transfers need.

  `stageSystemCall_prog` (SystemCallStaging.lean:270) is **71 instructions**.
  The routine's single address anchor — every other address here is derived
  from it — is `GuestAddrs.stage_system_call = 0x80053730`.  Its extent was
  re-derived from the linked guest ELF with `riscv64-elf-nm`, not transcribed:
  the next symbol is `GuestAddrs.stage_system_call_payload`, 284 bytes on, and
  `stageSystemCall_prog.length * 4 = 284` cross-checks that from the Program
  side (`sscProgL_spans_symbol`).

  This routine does **not** use an ABI stack frame: it spills `ra` and `s0` to
  two dedicated BSS cells (`ssc_saved_ra` / `ssc_saved_s0`), so `abiFrame_spec`
  does not apply and all 71 instructions are chained by hand.

  Zero-based index map (offsets are from the linked guest entry address):
    0–2    +0x00   spill `ra`  → `ssc_saved_ra`   (auipc/addi/sd)
    3–5    +0x0c   spill `s0`  → `ssc_saved_s0`   (auipc/addi/sd)
    6      +0x18   `mv t1, a0`                    (park the target ptr)
    7      +0x1c   `jal ra, account_read_record`  — NAMED RESIDUAL
    8      +0x20   `mv a0, t1`                    (restore the target ptr)
    9      +0x24   `beqz a2, +0xe0 → 56`          empty code ⇒ staging failure
    10     +0x28   `mv s0, a4`                    (park the output payload ptr)
    11–14  +0x2c   `system_call_returndata_len := 0`
    15–18  +0x3c   `system_call_mode := 1`
    19–21  +0x4c   `runtime_tx_auth_exec_fn := 0`
    22–24  +0x58   `rdg_halt_kind := 0`
    25     +0x64   `jal ra, stage_system_call_payload` — NAMED RESIDUAL
    26     +0x68   `bnez a0, +0xa0 → 56`          payload reject ⇒ staging failure
    27–30  +0x6c   `runtime_dispatcher_input_ptr := s0 + 8`
    31     +0x7c   `jal ra, runtime_dispatcher_call`  — NAMED RESIDUAL
    32–34  +0x80   `runtime_dispatcher_input_ptr := 0`
    35–38  +0x8c   `system_call_mode := 0`
    39–40  +0x9c   `a0 := &system_call_returndata`
    41–43  +0xa4   `a1 := [system_call_returndata_len]`
    44–46  +0xb0   `t1 := [rdg_halt_kind]`
    47     +0xbc   `beqz t1, +28 → 54`            halt_kind = STOP
    48–49  +0xc0   `li t0, 1 ; beq t1, t0, +20 → 54`   halt_kind = RETURN
    50–51  +0xc8   `li t0, 5 ; beq t1, t0, +12 → 54`   halt_kind = SELFDESTRUCT
    52–53  +0xd0   `li a2, 2 ; j +44 → 64`        execution failure
    54–55  +0xd8   `li a2, 0 ; j +36 → 64`        success
    56–59  +0xe0   staging-failure epilogue: `system_call_mode := 0`
    60–63  +0xf0   `a0 := &system_call_returndata ; li a1, 0 ; li a2, 1`
    64–66  +0x100  restore `s0` ← `ssc_saved_s0`
    67–69  +0x10c  restore `ra` ← `ssc_saved_ra`
    70     +0x118  `jalr x0, 0(ra)`

  There is **no backward transfer**: the routine is a pure forward DAG with two
  early exits into a shared failure epilogue and a three-way verdict cascade
  joining at index 64.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.Programs.SystemCallStaging

namespace EvmAsm.Codegen.SystemCallStagingBase

open EvmAsm.Rv64
open EvmAsm.Codegen

set_option maxRecDepth 8000

/-! ## Addresses -/

/-- Symbolic entry address of `stage_system_call` (the routine's one anchor). -/
abbrev B : Word := BitVec.ofNat 64 GuestAddrs.stage_system_call

/-- Entry address of the first residual callee, `account_read_record`. -/
abbrev ArdB : Word := BitVec.ofNat 64 GuestAddrs.account_read_record

/-- Entry address of the second residual callee, `stage_system_call_payload`. -/
abbrev SscpB : Word := BitVec.ofNat 64 GuestAddrs.stage_system_call_payload

/-- Entry address of the third residual callee, `runtime_dispatcher_call`. -/
abbrev RdcB : Word := BitVec.ofNat 64 GuestAddrs.runtime_dispatcher_call

/-! ### The BSS cells this routine owns -/

/-- `ssc_saved_ra` — the routine's private `ra` spill slot. -/
abbrev SscRa : Word := BitVec.ofNat 64 GuestAddrs.ssc_saved_ra

/-- `ssc_saved_s0` — the routine's private `s0` spill slot. -/
abbrev SscS0 : Word := BitVec.ofNat 64 GuestAddrs.ssc_saved_s0

/-- `system_call_mode` — the NoopHalt capture flag, set to 1 around the
    dispatcher call and cleared on every exit. -/
abbrev SccMode : Word := BitVec.ofNat 64 GuestAddrs.system_call_mode

/-- `system_call_returndata_len`. -/
abbrev SccLen : Word := BitVec.ofNat 64 GuestAddrs.system_call_returndata_len

/-- `system_call_returndata` — the buffer whose ADDRESS the routine returns
    in `a0` on every path. -/
abbrev SccData : Word := BitVec.ofNat 64 GuestAddrs.system_call_returndata

/-- `runtime_tx_auth_exec_fn`, zeroed before staging. -/
abbrev RtAuthFn : Word := BitVec.ofNat 64 GuestAddrs.runtime_tx_auth_exec_fn

/-- `rdg_halt_kind` — the exec-status discriminator (#11798 / #11815). -/
abbrev RdgHalt : Word := BitVec.ofNat 64 GuestAddrs.rdg_halt_kind

/-- `runtime_dispatcher_input_ptr`. -/
abbrev RdInPtr : Word := BitVec.ofNat 64 GuestAddrs.runtime_dispatcher_input_ptr

/-! ## The program and its `CodeReq` -/

/-- The routine's instruction list. -/
abbrev sscProgL : List Instr := stageSystemCall_prog

theorem sscProgL_len : sscProgL.length = 71 := by
  simp only [sscProgL, stageSystemCall_prog]; decide

/-- **Extent cross-check.**  `nm` puts the next symbol,
    `stage_system_call_payload`, 284 bytes past `stage_system_call`, and
    `71 * 4 = 284` — so the Program really does span the whole symbol rather
    than a prefix of it. -/
theorem sscProgL_spans_symbol :
    4 * sscProgL.length
      = GuestAddrs.stage_system_call_payload - GuestAddrs.stage_system_call := by
  rw [sscProgL_len]; decide

theorem sscProgL_bound : 4 * sscProgL.length < 2 ^ 64 := by
  rw [sscProgL_len]; norm_num

/-- The routine's own text.  **No callee union**: all three `jal` sites stand
    under named residuals, each of which carries its own `cr` obligation for
    the `jal` instruction itself (see `SystemCallStagingResiduals`).  This is
    the same posture `rhvCode` takes toward `execution_requests_hash`. -/
def sscCode : CodeReq := CodeReq.ofProg B sscProgL

/-- Address of instruction `k`. -/
def pc (k : Nat) : Word := B + BitVec.ofNat 64 (4 * k)

/-- Code membership for instruction `k` of the routine. -/
theorem mem_at (k : Nat) (ins : Instr) (a0 : Word)
    (hpc : a0 = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sscProgL.length)
    (hins : sscProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton a0 ins a = some i → sscCode a = some i :=
  CodeReq.ofProg_mem_at B a0 sscProgL k ins hpc hk hins sscProgL_bound

/-! ## pc arithmetic -/

private theorem word_shift (b : Word) (i j : Nat) :
    b + BitVec.ofNat 64 i + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem pc_add (k j : Nat) : (pc k : Word) + BitVec.ofNat 64 (4 * j) = pc (k + j) := by
  simp only [pc, word_shift, Nat.mul_add]

theorem pc_succ (k : Nat) : (pc k : Word) + 4 = pc (k + 1) := by
  have h : (4 : Word) = BitVec.ofNat 64 (4 * 1) := by decide
  rw [h, pc_add]

/-- `la` occupies two instructions, so `la_materialize_within`'s exit
    `pc + 8` is the index-`k+2` address. -/
theorem pc_add8 (k : Nat) : (pc k : Word) + 8 = pc (k + 2) := by
  have h : (8 : Word) = BitVec.ofNat 64 (4 * 2) := by decide
  rw [h, pc_add]


/-! ## `la` address bridges

    Each emitted `la` pair carries the CODEGEN-side immediates
    `Codegen.laHi/laLo sym (stage_system_call + 4k)`; `la_materialize_within`
    consumes the RV64-side `Rv64.laHi/laLo (pc k) target`.  That the two agree
    is checked by the kernel inside `SystemCallStagingSegments.la_step`, whose
    `hins` equations `decide` the emitted instruction against
    `.AUIPC rd (Rv64.laHi (pc k) target)`.  What is left here is the
    representability side condition, one `decide` per `la` site against the
    concrete linked layout.

    ⚠️ `Codegen.laHi`/`Codegen.laLo` and `Rv64.laHi`/`Rv64.laLo` are DIFFERENT
    functions with SWAPPED argument orders (`(sym, pc)` on Nats vs
    `(pc, target)` on `Word`s); both namespaces are open in this file. -/

theorem laRange_0 : laInRange (pc 0) SscRa := by decide

theorem laRange_3 : laInRange (pc 3) SscS0 := by decide

theorem laRange_12 : laInRange (pc 12) SccLen := by decide

theorem laRange_16 : laInRange (pc 16) SccMode := by decide

theorem laRange_19 : laInRange (pc 19) RtAuthFn := by decide

theorem laRange_22 : laInRange (pc 22) RdgHalt := by decide

theorem laRange_28 : laInRange (pc 28) RdInPtr := by decide

theorem laRange_32 : laInRange (pc 32) RdInPtr := by decide

theorem laRange_36 : laInRange (pc 36) SccMode := by decide

theorem laRange_39 : laInRange (pc 39) SccData := by decide

theorem laRange_41 : laInRange (pc 41) SccLen := by decide

theorem laRange_44 : laInRange (pc 44) RdgHalt := by decide

theorem laRange_57 : laInRange (pc 57) SccMode := by decide

theorem laRange_60 : laInRange (pc 60) SccData := by decide

theorem laRange_64 : laInRange (pc 64) SscS0 := by decide

theorem laRange_67 : laInRange (pc 67) SscRa := by decide

/-! ## Branch and jump targets

    Every offset below is read off the linked disassembly; the `decide`s are
    kernel-checked against the concrete `GuestAddrs` constants. -/

/-- `beqz a2, +0xe0` at index 9 (`B + 0x24`) — the empty-code gate — lands on
    the staging-failure epilogue at index 56 (`B + 0xe0`). -/
theorem pc_beq_emptycode :
    (pc 9 : Word) + signExtend13
        (brOff (GuestAddrs.stage_system_call + 224)
          (GuestAddrs.stage_system_call + 36)) = pc 56 := by
  have hs : signExtend13
      (brOff (GuestAddrs.stage_system_call + 224)
        (GuestAddrs.stage_system_call + 36)) = BitVec.ofNat 64 (4 * 47) := by decide
  rw [hs, pc_add]

/-- `bnez a0, +0xa0` at index 26 (`B + 0x68`) — the payload-reject gate —
    lands on the same staging-failure epilogue at index 56. -/
theorem pc_bne_payloadfail :
    (pc 26 : Word) + signExtend13
        (brOff (GuestAddrs.stage_system_call + 224)
          (GuestAddrs.stage_system_call + 104)) = pc 56 := by
  have hs : signExtend13
      (brOff (GuestAddrs.stage_system_call + 224)
        (GuestAddrs.stage_system_call + 104)) = BitVec.ofNat 64 (4 * 30) := by decide
  rw [hs, pc_add]

/-- `beqz t1, +28` at index 47 lands on the `li a2, 0` success verdict at 54. -/
theorem pc_beq_halt_stop :
    (pc 47 : Word) + signExtend13 (28 : BitVec 13) = pc 54 := by
  have hs : signExtend13 (28 : BitVec 13) = BitVec.ofNat 64 (4 * 7) := by decide
  rw [hs, pc_add]

/-- `beq t1, t0, +20` at index 49 (`t0 = 1`, RETURN) lands on 54. -/
theorem pc_beq_halt_return :
    (pc 49 : Word) + signExtend13 (20 : BitVec 13) = pc 54 := by
  have hs : signExtend13 (20 : BitVec 13) = BitVec.ofNat 64 (4 * 5) := by decide
  rw [hs, pc_add]

/-- `beq t1, t0, +12` at index 51 (`t0 = 5`, SELFDESTRUCT) lands on 54. -/
theorem pc_beq_halt_selfdestruct :
    (pc 51 : Word) + signExtend13 (12 : BitVec 13) = pc 54 := by
  have hs : signExtend13 (12 : BitVec 13) = BitVec.ofNat 64 (4 * 3) := by decide
  rw [hs, pc_add]

/-- `j +44` at index 53 joins the restore block at index 64. -/
theorem pc_jal_execfail_join :
    (pc 53 : Word) + signExtend21 (44 : BitVec 21) = pc 64 := by
  have hs : signExtend21 (44 : BitVec 21) = BitVec.ofNat 64 (4 * 11) := by decide
  rw [hs, pc_add]

/-- `j +36` at index 55 joins the restore block at index 64. -/
theorem pc_jal_ok_join :
    (pc 55 : Word) + signExtend21 (36 : BitVec 21) = pc 64 := by
  have hs : signExtend21 (36 : BitVec 21) = BitVec.ofNat 64 (4 * 9) := by decide
  rw [hs, pc_add]

/-! ### Call targets -/

/-- `jal ra, account_read_record` at index 7 (`B + 0x1c`). -/
theorem pc_jal_ard :
    (pc 7 : Word) +
      signExtend21 (jalOff GuestAddrs.account_read_record
        (GuestAddrs.stage_system_call + 28)) = ArdB := by
  unfold pc ArdB B jalOff signExtend21
  decide

/-- `jal ra, stage_system_call_payload` at index 25 (`B + 0x64`). -/
theorem pc_jal_sscp :
    (pc 25 : Word) +
      signExtend21 (jalOff GuestAddrs.stage_system_call_payload
        (GuestAddrs.stage_system_call + 100)) = SscpB := by
  unfold pc SscpB B jalOff signExtend21
  decide

/-- `jal ra, runtime_dispatcher_call` at index 31 (`B + 0x7c`). -/
theorem pc_jal_rdc :
    (pc 31 : Word) +
      signExtend21 (jalOff GuestAddrs.runtime_dispatcher_call
        (GuestAddrs.stage_system_call + 124)) = RdcB := by
  unfold pc RdcB B jalOff signExtend21
  decide

/-- All three call-site return addresses are 2-byte aligned, so each callee's
    `ret` (`jalr x0, 0(ra)`, which masks the low bit) lands exactly on the
    following instruction. -/
theorem ra_ard_aligned : ((pc 7 : Word) + 4 &&& ~~~(1 : Word)) = pc 7 + 4 := by
  rw [pc_succ]; unfold pc B; decide

theorem ra_sscp_aligned : ((pc 25 : Word) + 4 &&& ~~~(1 : Word)) = pc 25 + 4 := by
  rw [pc_succ]; unfold pc B; decide

theorem ra_rdc_aligned : ((pc 31 : Word) + 4 &&& ~~~(1 : Word)) = pc 31 + 4 := by
  rw [pc_succ]; unfold pc B; decide


end EvmAsm.Codegen.SystemCallStagingBase
