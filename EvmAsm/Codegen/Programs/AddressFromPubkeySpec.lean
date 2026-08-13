/-
  EvmAsm.Codegen.Programs.AddressFromPubkeySpec

  Verification support for `address_from_pubkey` (PR-K99), the ECRECOVER
  trailing step:

      address = keccak256(pubkey_x ‖ pubkey_y)[12:32]      (20 bytes)

  This module lands the FIRST increment of the whole-routine triple asked
  for by GH #12224: the ABI-frame decomposition.  `addressFromPubkey_prog`
  is byte-identically a standard leaf frame, so `abiFrame_spec_own`
  supplies the prologue, the epilogue, the `sp` round-trip and the `jalr`
  return without any per-instruction reasoning; what remains for the
  triple is the 18-instruction body.

  ⚠️ Deliberately NOT proved here (see #12224 for the analysis):

  * the body triple, whose keccak leg would be the FIRST consumer of
    `zkvm_keccak256_spec_within` anywhere in the repo, and
  * the per-iteration body triple of the 20-iteration digest→output copy
    loop (the `lbu`/`sb` byte step over the digest and output regions).

  The loop's CONTROL FLOW is no longer a gap: #12224 step 2 added the
  general combinator `beqLimitLoop_spec`/`beqCountLoop_spec`
  (`Rv64/SAsm/BeqLimitLoop.lean`) for the top-tested "count UP against a
  LIMIT REGISTER" shape (`beq x6, x7`) that matched none of the existing
  combinators (`countdownLoop_spec` hard-codes `beq ctr, x0`; `upLoop_spec`
  hard-codes `bgeu`), and `afpCopyLoop_spec` below instantiates it at this
  routine's real addresses, guard and step count.
  * ⚠️ `zkvm_keccak256_spec_within` fixes its output buffer to
    `List.replicate 32 0`, and this routine never zeroes `afp_digest` —
    so that becomes a precondition of the eventual whole-routine triple
    unless the keccak contract is first generalised over `out0`.
-/

import EvmAsm.Codegen.Programs.Address
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.BeqLimitLoop
import EvmAsm.Rv64.SAsm.CtrlSpecs

namespace EvmAsm.Codegen.AddressFromPubkeySpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm

/-- The saved-register frame of `address_from_pubkey`: `ra` at `0(sp)` and
    `s0` at `8(sp)`, in a 16-byte frame.  `s0` holds the caller's 20-byte
    output pointer across the `zkvm_keccak256` call. -/
def afpFrame : FrameDesc := [(.x1, (0 : BitVec 12)), (.x8, (8 : BitVec 12))]

/-- The body of `address_from_pubkey`: everything between the frame
    prologue and the frame epilogue — instructions 3..20 of
    `addressFromPubkey_prog`.

    Reading order: stash the output pointer in `s0`, set up the
    `zkvm_keccak256(a0 = pubkey, a1 = 64, a2 = afp_digest)` call, call it,
    then copy the 20 bytes at `afp_digest + 12` to the output, and set
    `a0 = 0`. -/
def afpBody : List Instr :=
  [ .MV .x8 .x11,
    .LI .x11 (64 : Word),
    .AUIPC .x12 (laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)),
    .ADDI .x12 .x12 (laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)),
    .JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_from_pubkey + 28)),
    .AUIPC .x5 (laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)),
    .ADDI .x5 .x5 (laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)),
    .LI .x6 (0 : Word),
    .LI .x7 (20 : Word),
    .BEQ .x6 .x7 (32 : BitVec 13),
    .ADDI .x28 .x5 (12 : BitVec 12),
    .ADD .x28 .x28 .x6,
    .LBU .x29 .x28 (0 : BitVec 12),
    .ADD .x28 .x8 .x6,
    .SB .x28 .x29 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (0 : Word) ]

/-- **The frame decomposition.**  `addressFromPubkey_prog` is byte-identically
    the standard leaf ABI frame `abiFrameProg (-16) 16 afpFrame afpBody`:

    * `addi sp, sp, -16`,
    * `sd ra, 0(sp)` / `sd s0, 8(sp)`,
    * the 18-instruction body,
    * `ld ra, 0(sp)` / `ld s0, 8(sp)`, `addi sp, sp, 16`,
    * `jalr x0, ra, 0`.

    This is what lets `abiFrame_spec_own` (`Rv64/SAsm/AbiFrameOwn.lean`)
    discharge the prologue and epilogue of the eventual whole-routine
    triple, leaving only `afpBody` to prove.  Kernel-checked by `rfl`, so
    it is a genuine byte-level identity and not a re-statement: if the
    emitted program drifts (a changed frame size, an extra saved
    register, a reordered prologue), this stops compiling. -/
theorem addressFromPubkey_prog_eq_abiFrame :
    addressFromPubkey_prog = abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) afpFrame afpBody :=
  rfl

/-- The body is 18 instructions, so the frame arithmetic
    `1 + frame.length + bodySteps + frame.length + 1 + 1` that
    `abiFrame_spec_own` reports is instantiated at `frame.length = 2`. -/
theorem afpBody_length : afpBody.length = 18 := by decide

theorem afpFrame_length : afpFrame.length = 2 := by decide

/-- Total program length, re-derived through the decomposition rather than
    copied: `1 + 2 + 18 + 2 + 1 + 1 = 25`, agreeing with the `#guard` on
    `addressFromPubkey_prog` in `Programs/Address.lean`. -/
theorem addressFromPubkey_prog_length : addressFromPubkey_prog.length = 25 := by decide

/-- `abiFrame_spec_own`'s `hframe` side condition: the frame saves `ra`
    first.  Discharged here so the eventual triple can cite it by name. -/
theorem afpFrame_cons : afpFrame = (.x1, (0 : BitVec 12)) :: [(.x8, (8 : BitVec 12))] := rfl

/-- `abiFrame_spec_own`'s `hne` side condition: no frame slot saves `x0`. -/
theorem afpFrame_ne_zero : ∀ p ∈ afpFrame, p.1 ≠ .x0 := by decide

/-- `abiFrame_spec_own`'s `hframeRestore` side condition: the `-16` of the
    prologue and the `+16` of the epilogue round-trip `sp` exactly, for
    every starting `sp0`.  Proved over all 2^64 stack pointers by
    bitvector reasoning, not by `decide`. -/
theorem afpFrame_restore (sp0 : Word) :
    (sp0 + signExtend12 (-16 : BitVec 12)) + signExtend12 (16 : BitVec 12) = sp0 := by
  have h : signExtend12 (-16 : BitVec 12) + signExtend12 (16 : BitVec 12) = (0 : Word) := by
    decide
  rw [BitVec.add_assoc, h]
  simp

/-! ## The digest→output copy loop (#12224 step 2)

  Program indices 10..19 of `addressFromPubkey_prog` are the byte copy

  ```
    10:  li   x6, 0                -- cursor
    11:  li   x7, 20               -- limit  (also the back-edge target!)
    12:  beq  x6, x7, .+32         -- HEADER: exit test, index 20
    13:  addi x28, x5, 12          -- fall-through
    14:  add  x28, x28, x6
    15:  lbu  x29, 0(x28)
    16:  add  x28, x8, x6
    17:  sb   x29, 0(x28)
    18:  addi x6, x6, 1
    19:  jal  x0, .-32             -- back-edge → index 11, NOT index 12
    20:  li   a0, 0                -- exit
  ```

  Everything below is geometry: it pins the header/exit/back-edge addresses
  against the real emitted program and discharges every hypothesis of
  `beqCountLoop_spec` except the per-iteration memory step, which stays an
  explicit named hypothesis (`hbody` of `afpCopyLoop_spec`) because it needs
  the digest/output byte regions that belong to the whole-routine triple.
-/

/-- Address of program instruction `k` of `address_from_pubkey` laid down at
    `base`. -/
def afpAt (base : Word) (k : Nat) : Word := base + BitVec.ofNat 64 (4 * k)

/-- The code requirement of the whole emitted routine at `base`. -/
def afpCr (base : Word) : CodeReq := CodeReq.ofProg base addressFromPubkey_prog

private theorem afpOfNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

private theorem afpAt_add (base : Word) (k j : Nat) :
    afpAt base k + BitVec.ofNat 64 (4 * j) = afpAt base (k + j) := by
  unfold afpAt
  rw [BitVec.add_assoc, afpOfNat_add]
  congr 2
  omega

private theorem afpAt_succ (base : Word) (k : Nat) : afpAt base k + 4 = afpAt base (k + 1) := by
  have h := afpAt_add base k 1
  rwa [show BitVec.ofNat 64 (4 * 1) = (4 : Word) from rfl] at h

/-- Instruction `k` of the routine is fetchable from the routine's own
    `CodeReq` — the `hguardMem`-shaped side condition the loop and
    straight-line combinators take. -/
private theorem afpMem (base : Word) (k : Nat) (instr : Instr)
    (hk : k < addressFromPubkey_prog.length)
    (hget : addressFromPubkey_prog.get ⟨k, hk⟩ = instr) :
    ∀ a i, CodeReq.singleton (afpAt base k) instr a = some i → afpCr base a = some i := by
  have m := CodeReq.ofProg_lookup_addr base addressFromPubkey_prog k (afpAt base k)
    hk (by decide) rfl
  rw [hget] at m
  exact CodeReq.singleton_mono m

/-- Drift guard: program index 12 really is the `beq x6, x7, .+32` exit
    test the loop combinator is applied to. -/
theorem afp_copy_guard_instr :
    addressFromPubkey_prog.get ⟨12, by decide⟩ = .BEQ .x6 .x7 (32 : BitVec 13) := rfl

/-- `beqCountLoop_spec`'s `hexit`: the taken guard lands on index 20. -/
theorem afp_copy_exit (base : Word) :
    afpAt base 12 + signExtend13 (32 : BitVec 13) = afpAt base 20 := by
  unfold afpAt
  rw [BitVec.add_assoc]
  congr 1

/-- ⚠️ The back-edge `jal x0, .-32` at index 19 lands on index **11**
    (`li x7, 20`), one instruction BEFORE the header at index 12.  This is
    why the loop's per-iteration body triple runs `hdr + 4 → hdr` in EIGHT
    steps (seven body instructions plus the re-executed limit reload) rather
    than seven: `beqLimitLoop_spec` takes an arbitrary body triple, so the
    reload is absorbed into it. -/
theorem afp_copy_backedge (base : Word) :
    afpAt base 19 + signExtend21 (-32 : BitVec 21) = afpAt base 11 := by
  unfold afpAt
  rw [BitVec.add_assoc]
  congr 1

/-- The two-instruction loop tail the body triple has to absorb, PROVED:
    from the back-edge at index 19 through the limit reload at index 11 to
    the header at index 12, restoring `x7 = 20` for the next guard.  This is
    the evidence that the `hbody` hypothesis of `afpCopyLoop_spec` is a
    statement about the real code path and not a vacuous one. -/
theorem afp_copy_tail_spec (base v7 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 2 (afpAt base 19) (afpAt base 12) (afpCr base)
      ((.x7 ↦ᵣ v7) ** R) ((.x7 ↦ᵣ (20 : Word)) ** R) := by
  have hjal := jal0_spec_pcFree (-32 : BitVec 21) (afpAt base 19)
    (P := (.x7 ↦ᵣ v7) ** R) (hP := pcFree_sepConj pcFree_regIs hR)
  rw [afp_copy_backedge base] at hjal
  have hjal' := cpsTripleWithin_extend_code
    (afpMem base 19 (.JAL .x0 (-32 : BitVec 21)) (by decide) rfl) hjal
  have hli := cpsTripleWithin_frameR R hR
    (li_spec_gen_within .x7 v7 (20 : Word) (afpAt base 11) (by decide))
  rw [afpAt_succ base 11] at hli
  have hli' := cpsTripleWithin_extend_code
    (afpMem base 11 (.LI .x7 (20 : Word)) (by decide) rfl) hli
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hjal' hli'

/-- **The copy loop of `address_from_pubkey`, as an instance of
    `beqCountLoop_spec`.**  Everything control-flow is discharged here
    against the real program — the guard instruction at index 12, its `.+32`
    exit landing on index 20, the fall-through at index 13, and the
    `20 * (8 + 1) + 1 = 181` step budget.

    The only remaining hypothesis is `hbody`, the per-iteration byte step
    (`addi/add/lbu/add/sb/addi` plus the back-edge and limit reload proved
    in `afp_copy_tail_spec`); it stays a named hypothesis because closing it
    needs the digest and output byte regions of the whole-routine triple,
    which is #12224 step 3. -/
theorem afpCopyLoop_spec (base : Word) (inv : Nat → Assertion)
    (hpcFree : ∀ n, (inv n).pcFree)
    (hbody : ∀ i, i < 20 →
      cpsTripleWithin 8 (afpAt base 13) (afpAt base 12) (afpCr base)
        ((.x6 ↦ᵣ BitVec.ofNat 64 i) ** (.x7 ↦ᵣ BitVec.ofNat 64 20) ** inv i)
        ((.x6 ↦ᵣ BitVec.ofNat 64 (i + 1)) ** (.x7 ↦ᵣ BitVec.ofNat 64 20)
          ** inv (i + 1))) :
    cpsTripleWithin 181 (afpAt base 12) (afpAt base 20) (afpCr base)
      ((.x6 ↦ᵣ BitVec.ofNat 64 0) ** (.x7 ↦ᵣ BitVec.ofNat 64 20) ** inv 0)
      ((.x6 ↦ᵣ BitVec.ofNat 64 20) ** (.x7 ↦ᵣ BitVec.ofNat 64 20) ** inv 20) :=
  beqCountLoop_spec (afpCr base) (afpAt base 12) (afpAt base 20) .x6 .x7
    (32 : BitVec 13) 8 20 inv (by decide) (afp_copy_exit base) hpcFree
    (afpMem base 12 (.BEQ .x6 .x7 (32 : BitVec 13)) (by decide) rfl)
    (fun i hi => by rw [afpAt_succ base 12]; exact hbody i hi)

end EvmAsm.Codegen.AddressFromPubkeySpec
