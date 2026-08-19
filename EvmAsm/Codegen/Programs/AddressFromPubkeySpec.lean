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

  * the body triple, whose keccak leg consumes `zkvm_keccak256_spec_within`,
    and
  * the per-iteration body triple of the 20-iteration digest→output copy
    loop (the `lbu`/`sb` byte step over the digest and output regions).

  ⚠️ THIS NOTE USED TO SAY the keccak leg "would be the FIRST consumer of
  `zkvm_keccak256_spec_within` anywhere in the repo".  That is STALE, and it
  overstated the risk: `block_hash_from_header_spec_within`
  (`Codegen/Programs/BlockHashFromHeaderSpec.lean:80`, rowed `.proven`) now
  consumes that contract directly, and demonstrates the whole surrounding
  pattern — `fullCode = wrapperCode.union keccakCode` with disjointness
  discharged from the wrapper length, `liftCode`/`callWithin_spec` for the
  cross-call, and a `frameSlotsSaved` epilogue.  So this leg is a PORT of a
  landed proof, not new ground.

  Templates for the copy leg, likewise already in the tree:
  * `TxSigningHashLegacyCopySpec.copyBody` — a per-iteration `lbu`/`sb` body
    triple with the hypothesis shape this one needs.  ⚠️ It counts DOWN while
    advancing pointers; this routine counts UP against a limit register and
    recomputes both addresses each iteration, so it is a port, not a copy.
  * `copyWin srcBytes orig i = srcBytes.take i ++ orig.drop i`
    (`SszPackBytesSAsm.lean`) is the right destination abstraction here, with
    `srcBytes = digest.drop 12`.  ⚠️ NOT
    `RlpFieldToU256BeLoopSAsm.copyWin bytes offset len i` despite its handy
    `offset`: it pads to a 32-byte RIGHT-ALIGNED window, which is the u256
    shape and does not fit this 20-byte left-aligned output.

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
    The precondition is HONEST rather than vacuous: the data section declares
    `afp_digest: .zero 32`, so it holds 32 zero bytes at image load and the
    FIRST call satisfies it — while any later call does not, since the buffer
    then holds a digest.  (The probe prologue zeroes the OUTPUT at `a1`, not
    `afp_digest`.)  So carrying it as a stated domain restriction is cheaper
    and more accurate than generalising the keccak contract.
-/

import EvmAsm.Codegen.Programs.Address
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.SAsm.BeqLimitLoop
import EvmAsm.Rv64.SAsm.CtrlSpecs
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.Tactics.XCancelStruct
import EvmAsm.Rv64.LaResolve
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge

-- ⚠️ `autoImplicit` off DELIBERATELY: while proving the keccak call leg, a bare
-- `Zk3` (private to `HashBridgeKeccakTop`, so not nameable here) was silently
-- auto-bound as a fresh universally-quantified `Word`, which would have made the
-- post talk about an ARBITRARY region instead of keccak's scratch buffer. It only
-- surfaced as a confusing unification failure two lemmas later. With this off it
-- is an unknown-identifier error at the point of use.
set_option autoImplicit false

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

-- ============================================================================
-- Increment 3a (#12224): the copy loop's DATA layer.
--
-- `afpCopyLoop_spec` above drives the loop but is parameterised by an arbitrary
-- invariant; the invariant the real routine maintains is "the first `i` of the 20
-- digest bytes have been written to the output". These are that window and its
-- boundary/step laws, proved ahead of the machine-level body triple exactly as
-- `afp_copy_tail_spec` was — so the remaining body triple is reduced to register
-- and memory stepping, with no list reasoning left in it.
--
-- ⚠️ Deliberately NOT reusing `RlpFieldToU256BeLoopSAsm.copyWin` despite its handy
-- `offset` parameter: that window pads to 32 bytes RIGHT-aligned
-- (`List.replicate (32 - len) 0 ++ …`), which is the u256 shape. This routine
-- writes 20 bytes LEFT-aligned into a 20-byte cell, so the shapes genuinely differ.
-- Its `copyWin_step` proof is still the idiom followed here
-- (`List.set_append_right` at the boundary).
-- ============================================================================


/-- Destination window after `i` of the 20 digest bytes have been copied.
    ⚠️ LEFT-aligned in a 20-byte cell, unlike `RlpFieldToU256BeLoopSAsm.copyWin`,
    which pads to a 32-byte RIGHT-aligned window (the u256 shape). -/
def afpWin (src orig : List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  src.take i ++ orig.drop i

theorem length_afpWin (src orig : List (BitVec 8)) (i : Nat)
    (hs : src.length = 20) (ho : orig.length = 20) (hi : i ≤ 20) :
    (afpWin src orig i).length = 20 := by
  simp only [afpWin, List.length_append, List.length_take, List.length_drop, hs, ho]
  omega

theorem afpWin_zero (src orig : List (BitVec 8)) : afpWin src orig 0 = orig := by
  simp [afpWin]

theorem afpWin_done (src orig : List (BitVec 8)) (hs : src.length = 20)
    (ho : orig.length = 20) : afpWin src orig 20 = src := by
  simp only [afpWin]
  rw [show List.drop 20 orig = [] from by
    apply List.drop_eq_nil_of_le; omega]
  simp [List.take_of_length_le (by omega : src.length ≤ 20)]

/-- One step of the window: writing `src[i]` at index `i` advances it. -/
theorem afpWin_step (src orig : List (BitVec 8)) (i : Nat)
    (hs : src.length = 20) (ho : orig.length = 20) (hi : i < 20) :
    (afpWin src orig i).set i (src[i]'(by omega)) = afpWin src orig (i + 1) := by
  have htk : (src.take i).length = i := by rw [List.length_take]; omega
  simp only [afpWin]
  rw [List.set_append_right (h := by omega)]
  rw [htk, Nat.sub_self]
  have hdrop : List.drop i orig = orig[i]'(by omega) :: List.drop (i + 1) orig := by
    rw [List.drop_eq_getElem_cons (by omega)]
  have htake1 : src.take (i + 1) = src.take i ++ [src[i]'(by omega)] := by
    rw [List.take_add_one]
    congr 1
    simp [List.getElem?_eq_getElem (show i < src.length by omega)]
  rw [htake1, List.append_assoc]
  congr 1
  rw [hdrop, List.set_cons_zero]
  rfl

-- Non-vacuity: the window really is "first `i` copied, rest original", left-aligned,
-- and the step law is a real advance rather than a definitional no-op.
#guard afpWin (List.replicate 20 (7 : BitVec 8)) (List.replicate 20 (1 : BitVec 8)) 0
  = List.replicate 20 (1 : BitVec 8)
#guard afpWin (List.replicate 20 (7 : BitVec 8)) (List.replicate 20 (1 : BitVec 8)) 20
  = List.replicate 20 (7 : BitVec 8)
#guard afpWin (List.replicate 20 (7 : BitVec 8)) (List.replicate 20 (1 : BitVec 8)) 3
  = [7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
#guard (afpWin (List.replicate 20 (7 : BitVec 8)) (List.replicate 20 (1 : BitVec 8)) 3).length = 20

-- ============================================================================
-- Increment 3b (#12224): the per-iteration BODY triple — `hbody` discharged.
--
-- `afpCopyLoop_spec` above is parameterised by an arbitrary invariant; this
-- section supplies the real one and proves the per-iteration step against the
-- actual six instructions at program indices 13-18, then composes with the
-- already-proved `afp_copy_tail_spec` (indices 19 and 11) for the 8-step total
-- the loop combinator asks for.
--
-- ⚠️ The two scratch registers `x28`/`x29` cannot be pinned to concrete values
-- in the invariant: at `i = 0` the loop is entered straight from the keccak
-- call, which leaves them arbitrary. So they enter as `regOwns` and are peeled
-- to a valuation with `cpsTripleWithin_peel_regOwns`.
-- ============================================================================

/-! ### Two missing `PCFree` instances

    `pcFree` resolves by instance synthesis (`Assertion.PCFree`), and there is no
    instance for `bytesRegion` or `regOwns` — so every frame rule over a byte
    region has to close its side goal by hand. These two supply them.

    ⚠️ They belong upstream beside the other instances in `Rv64/SepLogic.lean`,
    but `bytesRegion` lives in `Rv64/MemRegion.lean`, so declaring them there
    would rebuild every dependent of the memory-region tower; kept local until
    something else needs them. -/
private instance instPCFreeBytesRegion (base : Word) (bs : List (BitVec 8)) :
    Assertion.PCFree (bytesRegion base bs) := ⟨bytesRegion_pcFree base bs⟩

private instance instPCFreeRegOwns (rs : List Reg) :
    Assertion.PCFree (regOwns rs) := ⟨pcFree_regOwns rs⟩

/-- The two registers the copy body clobbers. Cannot be pinned in the invariant
    (see the note above), so they travel as `regOwns`. -/
def afpScratch : List Reg := [.x28, .x29]

/-- **The invariant the copy loop actually maintains**: the digest region intact,
    the output holding the first `i` of the 20 address bytes, and the two
    address-scratch registers merely owned. -/
def afpInv (dPtr oPtr : Word) (digest orig : List (BitVec 8)) : Nat → Assertion :=
  fun i =>
    ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
    bytesRegion dPtr digest **
    bytesRegion oPtr (afpWin (digest.drop 12) orig i) **
    regOwns afpScratch

theorem afpInv_pcFree (dPtr oPtr : Word) (digest orig : List (BitVec 8)) (i : Nat) :
    (afpInv dPtr oPtr digest orig i).pcFree := by
  unfold afpInv afpScratch
  pcFree

/-- The two scratch registers, once written, are just owned again. -/
private theorem afp_scratch_regOwns (a b : Word) :
    ∀ h, (((.x28 : Reg) ↦ᵣ a) ** ((.x29 : Reg) ↦ᵣ b)) h → (regOwns afpScratch) h := by
  intro h hp
  show (regOwn .x28 ** (regOwn .x29 ** empAssertion)) h
  rw [sepConj_emp_right' (regOwn .x29)]
  exact sepConj_mono (regIs_to_regOwn .x28 a) (regIs_to_regOwn .x29 b) h hp

/-- **The copy body, one iteration.**  Program indices 13-18 read digest byte
    `12 + i` and store it at output byte `i`, then bump the counter; indices 19
    and 11 (the back-edge and the limit reload) come from
    `afp_copy_tail_spec`.  Together these are exactly the `hbody` hypothesis of
    `afpCopyLoop_spec`, so applying the two closes the copy loop. -/
theorem afp_copy_body_spec (base dPtr oPtr : Word) (digest orig : List (BitVec 8))
    (hdig : digest.length = 32) (horig : orig.length = 20)
    (hdalign : dPtr.toNat % 8 = 0) (hoalign : oPtr.toNat % 8 = 0)
    (hdover : dPtr.toNat + 32 < 2 ^ 64) (hoover : oPtr.toNat + 20 < 2 ^ 64)
    (hdvalid : ∀ j, j < 32 → isValidByteAccess (dPtr + BitVec.ofNat 64 j) = true)
    (hovalid : ∀ j, j < 20 → isValidByteAccess (oPtr + BitVec.ofNat 64 j) = true)
    (i : Nat) (hi : i < 20) :
    cpsTripleWithin 8 (afpAt base 13) (afpAt base 12) (afpCr base)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20)
        ** afpInv dPtr oPtr digest orig i)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20)
        ** afpInv dPtr oPtr digest orig (i + 1)) := by
  have hsrclen : (digest.drop 12).length = 20 := by
    rw [List.length_drop, hdig]
  have hsi : i < (digest.drop 12).length := by omega
  have hwinlen : (afpWin (digest.drop 12) orig i).length = 20 :=
    length_afpWin _ _ i hsrclen horig (by omega)
  have hwi : i < (afpWin (digest.drop 12) orig i).length := by omega
  have hdi : 12 + i < digest.length := by omega
  have hdrop : (digest.drop 12)[i]'hsi = digest[12 + i]'hdi := by
    rw [List.getElem_drop]
  -- The byte written this iteration, and the window step it realises.
  have hwinstep : (afpWin (digest.drop 12) orig i).set i ((digest.drop 12)[i]'hsi)
      = afpWin (digest.drop 12) orig (i + 1) :=
    afpWin_step _ _ i hsrclen horig hi
  -- Address arithmetic: the routine recomputes both addresses from scratch.
  have h12 : signExtend12 (12 : BitVec 12) = (12 : Word) := by decide
  have h1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have hsrcaddr : dPtr + (12 : Word) + BitVec.ofNat 64 i
      = dPtr + BitVec.ofNat 64 (12 + i) := by
    rw [show (12 : Word) = BitVec.ofNat 64 12 from rfl, BitVec.add_assoc,
      afpOfNat_add]
  have hcount : BitVec.ofNat 64 i + (1 : Word) = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, afpOfNat_add]
  -- The six straight-line steps, over a concrete valuation of the scratch pair.
  have hsteps : ∀ v28 v29 : Word,
      cpsTripleWithin 6 (afpAt base 13) (afpAt base 19) (afpCr base)
        (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
          ((.x8 : Reg) ↦ᵣ oPtr) ** ((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29) **
          bytesRegion dPtr digest **
          bytesRegion oPtr (afpWin (digest.drop 12) orig i))
        (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
          ((.x8 : Reg) ↦ᵣ oPtr) **
          ((.x28 : Reg) ↦ᵣ (oPtr + BitVec.ofNat 64 i)) **
          ((.x29 : Reg) ↦ᵣ (((digest.drop 12)[i]'hsi).zeroExtend 64)) **
          bytesRegion dPtr digest **
          bytesRegion oPtr (afpWin (digest.drop 12) orig (i + 1))) := by
    intro v28 v29
    -- 13: addi x28, x5, 12
    have s13 := cpsTripleWithin_extend_code
      (afpMem base 13 (.ADDI .x28 .x5 (12 : BitVec 12)) (by decide) rfl)
      (addi_spec_gen_within .x28 .x5 v28 dPtr (12 : BitVec 12) (afpAt base 13)
        (by decide))
    rw [h12, afpAt_succ base 13] at s13
    have f13 := cpsTripleWithin_frameR
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion dPtr digest **
        bytesRegion oPtr (afpWin (digest.drop 12) orig i))
      (by pcFree) s13
    -- 14: add x28, x28, x6
    have s14 := cpsTripleWithin_extend_code
      (afpMem base 14 (.ADD .x28 .x28 .x6) (by decide) rfl)
      (add_spec_gen_rd_eq_rs1_within .x28 .x6 (dPtr + (12 : Word))
        (BitVec.ofNat 64 i) (afpAt base 14) (by decide))
    rw [hsrcaddr, afpAt_succ base 14] at s14
    have f14 := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        ((.x29 : Reg) ↦ᵣ v29) ** bytesRegion dPtr digest **
        bytesRegion oPtr (afpWin (digest.drop 12) orig i))
      (by pcFree) s14
    -- 15: lbu x29, 0(x28)
    have s15 := cpsTripleWithin_extend_code
      (afpMem base 15 (.LBU .x29 .x28 (0 : BitVec 12)) (by decide) rfl)
      (bytesRegion_lbu_within .x29 .x28 dPtr v29 (afpAt base 15) digest (12 + i)
        (by decide) hdalign hdi (by omega) (hdvalid (12 + i) (by omega)))
    rw [afpAt_succ base 15, ← hdrop] at s15
    have f15 := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion oPtr (afpWin (digest.drop 12) orig i))
      (by pcFree) s15
    -- 16: add x28, x8, x6
    have s16 := cpsTripleWithin_extend_code
      (afpMem base 16 (.ADD .x28 .x8 .x6) (by decide) rfl)
      (add_spec_gen_within .x28 .x8 .x6 oPtr (BitVec.ofNat 64 i)
        (dPtr + BitVec.ofNat 64 (12 + i)) (afpAt base 16) (by decide))
    rw [afpAt_succ base 16] at s16
    have f16 := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ dPtr) **
        ((.x29 : Reg) ↦ᵣ (((digest.drop 12)[i]'hsi).zeroExtend 64)) **
        bytesRegion dPtr digest **
        bytesRegion oPtr (afpWin (digest.drop 12) orig i))
      (by pcFree) s16
    -- 17: sb x29, 0(x28)
    have s17 := cpsTripleWithin_extend_code
      (afpMem base 17 (.SB .x28 .x29 (0 : BitVec 12)) (by decide) rfl)
      (bytesRegion_sb_within .x28 .x29 oPtr
        (((digest.drop 12)[i]'hsi).zeroExtend 64) (afpAt base 17)
        (afpWin (digest.drop 12) orig i) i hoalign hwi (by omega)
        (hovalid i (by omega)))
    rw [afpAt_succ base 17] at s17
    have hbyte : BitVec.truncate 8 (((digest.drop 12)[i]'hsi).zeroExtend 64)
        = digest[12 + i]'hdi := by simp
    rw [hdrop] at hwinstep
    rw [hbyte, hwinstep] at s17
    have f17 := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) **
        ((.x8 : Reg) ↦ᵣ oPtr) ** bytesRegion dPtr digest)
      (by pcFree) s17
    -- 18: addi x6, x6, 1
    have s18 := cpsTripleWithin_extend_code
      (afpMem base 18 (.ADDI .x6 .x6 (1 : BitVec 12)) (by decide) rfl)
      (addi_spec_gen_same_within .x6 (BitVec.ofNat 64 i) (1 : BitVec 12)
        (afpAt base 18) (by decide))
    rw [h1, hcount, afpAt_succ base 18] at s18
    have f18 := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        ((.x28 : Reg) ↦ᵣ (oPtr + BitVec.ofNat 64 i)) **
        ((.x29 : Reg) ↦ᵣ (((digest.drop 12)[i]'hsi).zeroExtend 64)) **
        bytesRegion dPtr digest **
        bytesRegion oPtr (afpWin (digest.drop 12) orig (i + 1)))
      (by pcFree) s18
    have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f13 f14
    have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f15
    have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f16
    have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c3 f17
    have c5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c4 f18
    exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun _ hp => by xcancel_struct hp) c5
  -- Append the back-edge and limit reload (indices 19 and 11), already proved.
  have htail := afp_copy_tail_spec base (BitVec.ofNat 64 20)
    (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
      ((.x8 : Reg) ↦ᵣ oPtr) **
      ((.x28 : Reg) ↦ᵣ (oPtr + BitVec.ofNat 64 i)) **
      ((.x29 : Reg) ↦ᵣ (((digest.drop 12)[i]'hsi).zeroExtend 64)) **
      bytesRegion dPtr digest **
      bytesRegion oPtr (afpWin (digest.drop 12) orig (i + 1)))
    (by pcFree)
  have hfull : ∀ v28 v29 : Word,
      cpsTripleWithin 8 (afpAt base 13) (afpAt base 12) (afpCr base)
        ((((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
          ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
          bytesRegion dPtr digest **
          bytesRegion oPtr (afpWin (digest.drop 12) orig i)) **
          (((.x28 : Reg) ↦ᵣ v28) ** ((.x29 : Reg) ↦ᵣ v29)))
        ((((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
          ((.x7 : Reg) ↦ᵣ (20 : Word)) **
          ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
          bytesRegion dPtr digest **
          bytesRegion oPtr (afpWin (digest.drop 12) orig (i + 1))) **
          regOwns afpScratch) := by
    intro v28 v29
    have hsF := cpsTripleWithin_frameR ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20)
      (by pcFree) (hsteps v28 v29)
    have hcomb := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xcancel_struct hp) hsF htail
    refine cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
      (fun h hq => sepConj_mono_right
        (afp_scratch_regOwns (oPtr + BitVec.ofNat 64 i)
          (((digest.drop 12)[i]'hsi).zeroExtend 64)) h (by xcancel_struct hq)) hcomb
  unfold afpInv
  refine cpsTripleWithin_weaken
    (P := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 i) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion dPtr digest **
        bytesRegion oPtr (afpWin (digest.drop 12) orig i))
      ** regOwns afpScratch)
    (Q := (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (i + 1)) **
        ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion dPtr digest **
        bytesRegion oPtr (afpWin (digest.drop 12) orig (i + 1)))
      ** regOwns afpScratch)
    (fun _ hp => by xcancel_struct hp) (fun _ hq => by xcancel_struct hq) ?_
  refine cpsTripleWithin_peel_regOwns afpScratch (by decide) (fun vf => ?_)
  simp only [afpScratch, regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) (hfull (vf .x28) (vf .x29))


/-- **The copy loop of `address_from_pubkey`, CLOSED.**  `afpCopyLoop_spec`'s only
    remaining hypothesis was `hbody`; `afp_copy_body_spec` is it, so the loop is
    now a theorem about the real code rather than a driver.

    Read off the post: after 181 steps the 20-byte output window at `s0` holds
    `digest.drop 12` — bytes 12-31 of the keccak digest, which is exactly the
    `keccak256(pubkey)[12:32]` slice the address-derivation formula names. The
    original output contents are gone (`afpWin_done`), and the digest region is
    intact.

    What remains for the whole-routine triple (#12224 legs b, c) is the keccak
    call that establishes `bytesRegion afp_digest digest` in the first place, and
    the ABI frame composition. -/
theorem afp_copy_loop_spec (base dPtr oPtr : Word) (digest orig : List (BitVec 8))
    (hdig : digest.length = 32) (horig : orig.length = 20)
    (hdalign : dPtr.toNat % 8 = 0) (hoalign : oPtr.toNat % 8 = 0)
    (hdover : dPtr.toNat + 32 < 2 ^ 64) (hoover : oPtr.toNat + 20 < 2 ^ 64)
    (hdvalid : ∀ j, j < 32 → isValidByteAccess (dPtr + BitVec.ofNat 64 j) = true)
    (hovalid : ∀ j, j < 20 → isValidByteAccess (oPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 181 (afpAt base 12) (afpAt base 20) (afpCr base)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion dPtr digest ** bytesRegion oPtr orig ** regOwns afpScratch)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 20) ** ((.x7 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion dPtr digest ** bytesRegion oPtr (digest.drop 12) **
        regOwns afpScratch) := by
  have hsrclen : (digest.drop 12).length = 20 := by rw [List.length_drop, hdig]
  have hloop := afpCopyLoop_spec base (afpInv dPtr oPtr digest orig)
    (fun n => afpInv_pcFree dPtr oPtr digest orig n)
    (fun i hi => afp_copy_body_spec base dPtr oPtr digest orig hdig horig
      hdalign hoalign hdover hoover hdvalid hovalid i hi)
  rw [show afpInv dPtr oPtr digest orig 0
      = (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
          bytesRegion dPtr digest ** bytesRegion oPtr orig ** regOwns afpScratch) from by
    unfold afpInv; rw [afpWin_zero]] at hloop
  rw [show afpInv dPtr oPtr digest orig 20
      = (((.x5 : Reg) ↦ᵣ dPtr) ** ((.x8 : Reg) ↦ᵣ oPtr) **
          bytesRegion dPtr digest ** bytesRegion oPtr (digest.drop 12) **
          regOwns afpScratch) from by
    unfold afpInv; rw [afpWin_done _ _ hsrclen horig]] at hloop
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hloop

-- Non-vacuity for the loop's data layer: the window really advances, and at the
-- end it is the digest slice rather than the original buffer. (The register and
-- memory stepping is checked by the build; these guard the ABSTRACTION.)
#guard afpWin (List.replicate 20 (9 : BitVec 8)) (List.replicate 20 (4 : BitVec 8)) 1
    = (9 : BitVec 8) :: List.replicate 19 (4 : BitVec 8)
#guard afpWin ((List.replicate 12 (0 : BitVec 8) ++ List.replicate 20 (9 : BitVec 8)).drop 12)
    (List.replicate 20 (4 : BitVec 8)) 20 = List.replicate 20 (9 : BitVec 8)


-- ============================================================================
-- Increment 3c (#12224): everything from the keccak RETURN to the loop exit.
--
-- Indices 8-11 rematerialise the digest pointer with an `la` pair and zero the
-- loop counters; composing with `afp_copy_loop_spec` gives a single triple from
-- the keccak return site (index 8) to the loop exit (index 20).
--
-- ⚠️ TWO `laHi`s EXIST, with SWAPPED ARGUMENT ORDER AND DIFFERENT TYPES:
-- `Codegen.laHi (sym pc : Nat)` — what the emitter puts in the program — and
-- `Rv64.laHi (pc target : Word)`, which is what `la_resolve` is stated about.
-- They are bridged PER SITE by `decide`, following the precedent in
-- `Proofs/HashBridgeKeccakSetup.lean` (`la_zk3_hi`/`la_zk3_lo`). A proof that
-- reaches for `la_resolve` with the emitter's immediate will fail to unify with
-- no hint that two different functions are in play.
-- ============================================================================

/-- The routine's own guest address: these lemmas are NOT base-generic, because
    the `la` immediates are baked against this pc. -/
private def afpB : Word := (GuestAddrs.address_from_pubkey : Word)

/-- The digest scratch buffer's guest address. -/
private def afpDigestPtr : Word := (GuestAddrs.afp_digest : Word)

private theorem afp_la_hi :
    Codegen.laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)
      = Rv64.laHi (afpB + 32) afpDigestPtr := by decide

private theorem afp_la_lo :
    Codegen.laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32)
      = Rv64.laLo (afpB + 32) afpDigestPtr := by decide

private theorem afp_la_range : laInRange (afpB + 32) afpDigestPtr := by decide

private theorem afpAt_8 : afpAt afpB 8 = afpB + 32 := by
  unfold afpAt; rfl

/-- **Indices 8-11: rematerialise the digest pointer and arm the loop.**
    `auipc`/`addi` reconstruct `afp_digest` in `t0`, then the counter and limit
    are loaded, landing on the loop guard at index 12. -/
theorem afp_loop_setup_spec (v5 v6 v7 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 4 (afpAt afpB 8) (afpAt afpB 12) (afpCr afpB)
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** R)
      (((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ (0 : Word)) **
        ((.x7 : Reg) ↦ᵣ (20 : Word)) ** R) := by
  -- 8: auipc t0, %pcrel_hi(afp_digest)
  have s8 := cpsTripleWithin_extend_code
    (afpMem afpB 8 (.AUIPC .x5 (Codegen.laHi GuestAddrs.afp_digest
      (GuestAddrs.address_from_pubkey + 32))) (by decide) rfl)
    (auipc_spec_gen_within .x5 v5
      (Codegen.laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32))
      (afpAt afpB 8) (by decide))
  rw [afpAt_succ afpB 8] at s8
  have f8 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** R) (by pcFree; exact hR) s8
  -- 9: addi t0, t0, %pcrel_lo(1b) — completes the `la`
  have s9 := cpsTripleWithin_extend_code
    (afpMem afpB 9 (.ADDI .x5 .x5 (Codegen.laLo GuestAddrs.afp_digest
      (GuestAddrs.address_from_pubkey + 32))) (by decide) rfl)
    (addi_spec_gen_same_within .x5
      (afpAt afpB 8 + ((((Codegen.laHi GuestAddrs.afp_digest
        (GuestAddrs.address_from_pubkey + 32)).zeroExtend 32 : BitVec 32)
        <<< 12).signExtend 64))
      (Codegen.laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 32))
      (afpAt afpB 9) (by decide))
  rw [afpAt_succ afpB 9] at s9
  -- The `la` round-trip, once the emitter's immediates are bridged to `Rv64`.
  have hla : afpAt afpB 8 + ((((Codegen.laHi GuestAddrs.afp_digest
        (GuestAddrs.address_from_pubkey + 32)).zeroExtend 32 : BitVec 32)
        <<< 12).signExtend 64)
      + signExtend12 (Codegen.laLo GuestAddrs.afp_digest
        (GuestAddrs.address_from_pubkey + 32))
      = afpDigestPtr := by
    rw [afp_la_hi, afp_la_lo, afpAt_8]
    exact la_resolve (afpB + 32) afpDigestPtr afp_la_range
  rw [hla] at s9
  have f9 := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) ** R) (by pcFree; exact hR) s9
  -- 10: li a2, 0   (loop counter)
  have s10 := cpsTripleWithin_extend_code
    (afpMem afpB 10 (.LI .x6 (0 : Word)) (by decide) rfl)
    (li_spec_gen_within .x6 v6 (0 : Word) (afpAt afpB 10) (by decide))
  rw [afpAt_succ afpB 10] at s10
  have f10 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x7 : Reg) ↦ᵣ v7) ** R)
    (by pcFree; exact hR) s10
  -- 11: li a3, 20  (loop limit)
  have s11 := cpsTripleWithin_extend_code
    (afpMem afpB 11 (.LI .x7 (20 : Word)) (by decide) rfl)
    (li_spec_gen_within .x7 v7 (20 : Word) (afpAt afpB 11) (by decide))
  rw [afpAt_succ afpB 11] at s11
  have f11 := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ (0 : Word)) ** R)
    (by pcFree; exact hR) s11
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f8 f9
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f10
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f11
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c3


/-- **From the keccak return to the loop exit, in one triple.**  Composes
    `afp_loop_setup_spec` (indices 8-11) with `afp_copy_loop_spec` (12-20).

    This is the whole second half of `address_from_pubkey`'s body: given the
    digest that the keccak call left in `afp_digest`, the 20-byte output window
    ends up holding `digest.drop 12` — `keccak256(pubkey)[12:32]`.  The three
    registers the setup rematerialises (`t0`, and the two loop counters) enter
    unconstrained, so this composes directly onto whatever the call site leaves.

    ⚠️ What is left of #12224 is now exactly TWO things: the `callWithin` step at
    index 7 (with its `zkvm_keccak256_spec_within` side conditions, discharged at
    `N = 0`, `rem = 64` for the 64-byte public key), and the ABI frame
    composition, for which `addressFromPubkey_prog_eq_abiFrame` and
    `afpFrame_restore` are already in place. -/
theorem afp_after_keccak_spec (oPtr : Word) (digest orig : List (BitVec 8))
    (v5 v6 v7 : Word)
    (hdig : digest.length = 32) (horig : orig.length = 20)
    (hdalign : afpDigestPtr.toNat % 8 = 0) (hoalign : oPtr.toNat % 8 = 0)
    (hdover : afpDigestPtr.toNat + 32 < 2 ^ 64) (hoover : oPtr.toNat + 20 < 2 ^ 64)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (afpDigestPtr + BitVec.ofNat 64 j) = true)
    (hovalid : ∀ j, j < 20 → isValidByteAccess (oPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 185 (afpAt afpB 8) (afpAt afpB 20) (afpCr afpB)
      (((.x5 : Reg) ↦ᵣ v5) ** ((.x6 : Reg) ↦ᵣ v6) ** ((.x7 : Reg) ↦ᵣ v7) **
        ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion afpDigestPtr digest ** bytesRegion oPtr orig **
        regOwns afpScratch)
      (((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion afpDigestPtr digest ** bytesRegion oPtr (digest.drop 12) **
        regOwns afpScratch) := by
  have hsetup := afp_loop_setup_spec v5 v6 v7
    (((.x8 : Reg) ↦ᵣ oPtr) ** bytesRegion afpDigestPtr digest **
      bytesRegion oPtr orig ** regOwns afpScratch) (by pcFree)
  have hloop := afp_copy_loop_spec afpB afpDigestPtr oPtr digest orig hdig horig
    hdalign hoalign hdover hoover hdvalid hovalid
  -- The setup's `0`/`20` literals are the loop's `BitVec.ofNat 64 0`/`… 20`.
  have h0 : (0 : Word) = BitVec.ofNat 64 0 := rfl
  have h20 : (20 : Word) = BitVec.ofNat 64 20 := rfl
  rw [h0, h20] at hsetup
  have hcomb := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hsetup hloop
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcomb


/-! ## Increment 3d (#12224): the keccak call's argument setup (indices 3-6)

    `mv s0, a1` parks the caller's OUTPUT pointer (where the 20-byte address
    goes) in `s0`, freeing `a1` for the keccak length argument; `li a1, 64` is
    the public key's length; the `la` pair puts `&afp_digest` in `a2`. `a0` is
    left alone — it still holds the public-key pointer the caller passed, which
    becomes keccak's input pointer.

    Second `la` site, so a second pair of per-site bridges (pc = base + 20 here,
    against base + 32 for the loop setup). -/

private theorem afp_la_hi_20 :
    Codegen.laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)
      = Rv64.laHi (afpB + 20) afpDigestPtr := by decide

private theorem afp_la_lo_20 :
    Codegen.laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20)
      = Rv64.laLo (afpB + 20) afpDigestPtr := by decide

private theorem afp_la_range_20 : laInRange (afpB + 20) afpDigestPtr := by decide

private theorem afpAt_5 : afpAt afpB 5 = afpB + 20 := by
  unfold afpAt; rfl

/-- **Indices 3-6: keccak's three arguments.**  On exit `a0` is untouched (the
    public-key pointer), `a1 = 64`, `a2 = &afp_digest`, and `s0` holds the
    caller's output pointer for the copy loop to use later. -/
theorem afp_call_setup_spec (a1Val v8 v12 : Word) (R : Assertion) (hR : R.pcFree) :
    cpsTripleWithin 4 (afpAt afpB 3) (afpAt afpB 7) (afpCr afpB)
      (((.x8 : Reg) ↦ᵣ v8) ** ((.x11 : Reg) ↦ᵣ a1Val) **
        ((.x12 : Reg) ↦ᵣ v12) ** R)
      (((.x8 : Reg) ↦ᵣ a1Val) ** ((.x11 : Reg) ↦ᵣ (64 : Word)) **
        ((.x12 : Reg) ↦ᵣ afpDigestPtr) ** R) := by
  -- 3: mv s0, a1
  have s3 := cpsTripleWithin_extend_code
    (afpMem afpB 3 (.MV .x8 .x11) (by decide) rfl)
    (mv_spec_gen_within .x8 .x11 a1Val v8 (afpAt afpB 3) (by decide))
  rw [afpAt_succ afpB 3] at s3
  have f3 := cpsTripleWithin_frameR (((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcFree; exact hR) s3
  -- 4: li a1, 64
  have s4 := cpsTripleWithin_extend_code
    (afpMem afpB 4 (.LI .x11 (64 : Word)) (by decide) rfl)
    (li_spec_gen_within .x11 a1Val (64 : Word) (afpAt afpB 4) (by decide))
  rw [afpAt_succ afpB 4] at s4
  have f4 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a1Val) ** ((.x12 : Reg) ↦ᵣ v12) ** R)
    (by pcFree; exact hR) s4
  -- 5: auipc a2, %pcrel_hi(afp_digest)
  have s5 := cpsTripleWithin_extend_code
    (afpMem afpB 5 (.AUIPC .x12 (Codegen.laHi GuestAddrs.afp_digest
      (GuestAddrs.address_from_pubkey + 20))) (by decide) rfl)
    (auipc_spec_gen_within .x12 v12
      (Codegen.laHi GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20))
      (afpAt afpB 5) (by decide))
  rw [afpAt_succ afpB 5] at s5
  have f5 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a1Val) ** ((.x11 : Reg) ↦ᵣ (64 : Word)) ** R)
    (by pcFree; exact hR) s5
  -- 6: addi a2, a2, %pcrel_lo(1b)
  have s6 := cpsTripleWithin_extend_code
    (afpMem afpB 6 (.ADDI .x12 .x12 (Codegen.laLo GuestAddrs.afp_digest
      (GuestAddrs.address_from_pubkey + 20))) (by decide) rfl)
    (addi_spec_gen_same_within .x12
      (afpAt afpB 5 + ((((Codegen.laHi GuestAddrs.afp_digest
        (GuestAddrs.address_from_pubkey + 20)).zeroExtend 32 : BitVec 32)
        <<< 12).signExtend 64))
      (Codegen.laLo GuestAddrs.afp_digest (GuestAddrs.address_from_pubkey + 20))
      (afpAt afpB 6) (by decide))
  rw [afpAt_succ afpB 6] at s6
  have hla : afpAt afpB 5 + ((((Codegen.laHi GuestAddrs.afp_digest
        (GuestAddrs.address_from_pubkey + 20)).zeroExtend 32 : BitVec 32)
        <<< 12).signExtend 64)
      + signExtend12 (Codegen.laLo GuestAddrs.afp_digest
        (GuestAddrs.address_from_pubkey + 20))
      = afpDigestPtr := by
    rw [afp_la_hi_20, afp_la_lo_20, afpAt_5]
    exact la_resolve (afpB + 20) afpDigestPtr afp_la_range_20
  rw [hla] at s6
  have f6 := cpsTripleWithin_frameR
    (((.x8 : Reg) ↦ᵣ a1Val) ** ((.x11 : Reg) ↦ᵣ (64 : Word)) ** R)
    (by pcFree; exact hR) s6
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) f3 f4
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c1 f5
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xcancel_struct hp) c2 f6
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c3


open EvmAsm.Codegen.Proofs

/-! ⚠️ `Zk3` — keccak's 200-byte scratch base — is `private abbrev` in
    `HashBridgeKeccakTop` (and privately RE-DECLARED in four more files). The
    callee's `keccakCallerPre`/`keccakCallerPost` mention it, so any caller that
    has to match those assertions atom-for-atom needs the same spelling: writing
    the unfolded `BitVec.ofNat 64 GuestAddrs.zk3_state` is `rfl`-equal but not
    syntactically equal, and the sep-conj cancellation matches atoms
    syntactically. Hence `open private` rather than a re-spelling.

    A public name for this address (it is the same one in all five files) would
    remove the need for this. -/
open private Zk3 from EvmAsm.Codegen.Proofs.HashBridgeKeccakTop

private instance instPCFreeRegsAt (frame : FrameDesc) (vals : Reg → Word) :
    Assertion.PCFree (regsAt frame vals) := ⟨pcFree_regsAt _ _⟩

private instance instPCFreeFrameSlotsOwn (frame : FrameDesc) (sp : Word) :
    Assertion.PCFree (frameSlotsOwn frame sp) := ⟨pcFree_frameSlotsOwn _ _⟩

private instance instPCFreeFrameSlotsSaved (frame : FrameDesc) (sp : Word)
    (vals : Reg → Word) :
    Assertion.PCFree (frameSlotsSaved frame sp vals) := ⟨pcFree_frameSlotsSaved _ _ _⟩

/-! ## Increment 3e (#12224): the keccak call itself (index 7)

    The cross-routine step, over the UNION of this routine's code and the
    keccak256 implementation's — `callWithin_spec` needs both reachable from one
    `CodeReq`, and the two ranges are disjoint by construction.

    ⭐ INSTANTIATION: keccak's contract is parameterised by `N` absorb blocks and
    a `rem` tail with `input.length = 136 * N + rem`; a 64-byte public key gives
    `N = 0`, `rem = 64`, comfortably inside `rem ≤ 135`. So the sponge never
    takes a full-block iteration here — the whole hash is one padded block.

    ⭐ WHICH SIDE CONDITIONS SURVIVE: of the callee's twenty, the fifteen about
    its own 200-byte `zk3_state` scratch region are facts about the LINKED
    LAYOUT, and are discharged here by `decide` rather than pushed onto callers.
    Only the four that mention the caller's input pointer remain hypotheses,
    plus `os.length = 200` for the sponge state. That is the honest split: a
    caller can satisfy the remaining ones, and cannot do anything about the
    others. -/

abbrev afpK : Word := (GuestAddrs.zkvm_keccak256 : Word)
abbrev afpKeccakCode : CodeReq := CodeReq.ofProg afpK zkvmKeccak256_prog
abbrev afpFullCode : CodeReq := (afpCr afpB).union afpKeccakCode

theorem afp_wrapper_mem : ∀ a i, afpCr afpB a = some i → afpFullCode a = some i :=
  fun a i h => CodeReq.union_mono_left a i h

theorem afp_keccak_mem : ∀ a i, afpKeccakCode a = some i → afpFullCode a = some i := by
  intro a i h
  exact CodeReq.mono_union_right
    (CodeReq.Disjoint.ofProg_ranges afpB afpK addressFromPubkey_prog
      zkvmKeccak256_prog
      (by rw [addressFromPubkey_prog_length]; decide)
      (by decide)
      (by rw [addressFromPubkey_prog_length]; decide))
    (fun _ _ h => h) a i h

private theorem afpAt_7_succ : afpAt afpB 7 + (4 : Word) = afpAt afpB 8 :=
  afpAt_succ afpB 7

set_option maxRecDepth 100000 in
/-- **Index 7: `jal ra, zkvm_keccak256`.**  On return the digest of the 64-byte
    public key is in `afp_digest`, which is precisely the precondition
    `afp_after_keccak_spec` needs. -/
theorem afp_keccak_call_spec (sp0 vRa inputBase : Word)
    (input : List (BitVec 8)) (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hinput : input.length = 64) (hos : os.length = 200)
    (hb8i : (keccakAbsorbCursor inputBase 0).toNat % 8 = 0)
    (hoveri : ∀ n, n < 64 →
      (keccakAbsorbCursor inputBase 0).toNat + (64 - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < 64 →
      isValidByteAccess
        (keccakAbsorbCursor inputBase 0 + BitVec.ofNat 64 (64 - (n + 1))) = true) :
    cpsTripleWithin (1 + (5 + keccakBodyFuel 0 64 + 6))
        (afpAt afpB 7) (afpAt afpB 8) afpFullCode
      (((.x1 : Reg) ↦ᵣ vRa) **
        ((.x2 : Reg) ↦ᵣ sp0) **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        keccakCallerPre inputBase (64 : Word) afpDigestPtr
          v28 v29 os input (List.replicate 32 (0 : BitVec 8)) A)
      (((.x1 : Reg) ↦ᵣ (afpAt afpB 8)) **
        ((.x2 : Reg) ↦ᵣ sp0) **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        frameSlotsSaved keccakFrame (sp0 + signExtend12 (-32 : BitVec 12))
          (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPost inputBase afpDigestPtr input 0 64 A) := by
  -- The callee's caller-visible footprint, named so `callWithin_spec`'s `hP`
  -- has something to elaborate against (an unpinned `P` makes it unsolvable).
  have hlen : input.length = keccakAbsorbStep * 0 + 64 := by
    rw [hinput]; decide
  have hcallee := zkvm_keccak256_spec_within sp0 (afpAt afpB 8)
    inputBase afpDigestPtr input 0 64 v8 v9 v18 v20 v28 v29 os A hA
    (by decide) hlen (by decide) hos (by decide) (by decide) (by decide) (by decide)
    hb8i (by decide) hoveri (by decide) hvalidi (by decide) (by decide) (by decide)
  have hcalleeFull := cpsTripleWithin_extend_code afp_keccak_mem hcallee
  have hmem : ∀ a i, CodeReq.singleton (afpAt afpB 7) (.JAL .x1
      (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_from_pubkey + 28)))
      a = some i → afpFullCode a = some i := by
    intro a i h
    exact afp_wrapper_mem a i
      (afpMem afpB 7 (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
        (GuestAddrs.address_from_pubkey + 28))) (by decide) rfl a i h)
  have hcall := callWithin_spec (cr := afpFullCode)
    (P := ((.x2 : Reg) ↦ᵣ sp0) **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      frameSlotsOwn keccakFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
      keccakCallerPre inputBase (64 : Word) afpDigestPtr
        v28 v29 os input (List.replicate 32 (0 : BitVec 8)) A)
    (Q := ((.x2 : Reg) ↦ᵣ sp0) **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      frameSlotsSaved keccakFrame (sp0 + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase afpDigestPtr input 0 64 A)
    (afpAt afpB 7) afpK vRa
    (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.address_from_pubkey + 28))
    (5 + keccakBodyFuel 0 64 + 6)
    (by decide)
    hmem
    (pcFree_sepConj pcFree_regIs
      (pcFree_sepConj (pcFree_regsAt _ _)
        (pcFree_sepConj (pcFree_frameSlotsOwn _ _)
          (keccakCallerPre_pcFree _ _ _ _ _ _ _ _ _ hA))))
    (by
      rw [afpAt_7_succ]
      exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
        (fun _ hq => by xcancel_struct hq) hcalleeFull)
  rw [afpAt_7_succ] at hcall
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcall


/-! ### Non-vacuity of the call leg's caller-side hypotheses

    `afp_keccak_call_spec` keeps three hypotheses about the caller's input
    pointer. A triple under unsatisfiable hypotheses proves nothing, so both
    directions are witnessed here: the bundle HOLDS for an 8-aligned address in a
    valid data region, and its alignment clause FAILS one byte over — so it is
    not vacuously true of every address.

    (`afp_digest` is used as a convenient concrete valid address; this does not
    suggest it is ever the routine's input.) -/

set_option maxRecDepth 100000 in
private theorem afp_call_hyps_satisfiable :
    (keccakAbsorbCursor afpDigestPtr 0).toNat % 8 = 0
    ∧ (∀ n, n < 64 →
        (keccakAbsorbCursor afpDigestPtr 0).toNat + (64 - (n + 1)) < 2 ^ 64)
    ∧ (∀ n, n < 64 → isValidByteAccess
        (keccakAbsorbCursor afpDigestPtr 0 + BitVec.ofNat 64 (64 - (n + 1)))
        = true) :=
  ⟨by decide, by decide, by decide⟩

/-- Negative control for the alignment clause: one byte past the aligned base it
    is FALSE, so `afp_call_hyps_satisfiable` is a real restriction rather than a
    tautology about all addresses. -/
private theorem afp_call_hyps_not_trivial :
    ¬ ((keccakAbsorbCursor (afpDigestPtr + 1) 0).toNat % 8 = 0) := by decide


/-! ## Increment 3f (#12224): matching the callee's register handover

    `afp_after_keccak_spec` wants `t0`/`t1`/`t2` as concrete values, but keccak
    returns them as OWNERSHIP — `regOwn .x5` in `keccakCallerPost` and `x6`/`x7`
    at the head of `regOwns keccakCsrsRestNoX5`. This variant takes the
    ownership form, and lives over the union `CodeReq` so it can be composed
    with the call. -/

theorem afp_after_keccak_own (oPtr : Word) (digest orig : List (BitVec 8))
    (hdig : digest.length = 32) (horig : orig.length = 20)
    (hdalign : afpDigestPtr.toNat % 8 = 0) (hoalign : oPtr.toNat % 8 = 0)
    (hdover : afpDigestPtr.toNat + 32 < 2 ^ 64) (hoover : oPtr.toNat + 20 < 2 ^ 64)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (afpDigestPtr + BitVec.ofNat 64 j) = true)
    (hovalid : ∀ j, j < 20 → isValidByteAccess (oPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin 185 (afpAt afpB 8) (afpAt afpB 20) afpFullCode
      ((((.x8 : Reg) ↦ᵣ oPtr) **
          bytesRegion afpDigestPtr digest ** bytesRegion oPtr orig **
          regOwns afpScratch) **
        regOwns [(.x5 : Reg), (.x6 : Reg), (.x7 : Reg)])
      (((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion afpDigestPtr digest ** bytesRegion oPtr (digest.drop 12) **
        regOwns afpScratch) := by
  refine cpsTripleWithin_peel_regOwns [(.x5 : Reg), (.x6 : Reg), (.x7 : Reg)]
    (by decide) (fun vf => ?_)
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  have h := cpsTripleWithin_extend_code afp_wrapper_mem
    (afp_after_keccak_spec oPtr digest orig (vf .x5) (vf .x6) (vf .x7)
      hdig horig hdalign hoalign hdover hoover hdvalid hovalid)
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) h


/-! ## Increment 3g (#12224): the call and the copy, joined (indices 7-20)

    The interesting part of this join is the REGISTER HANDOVER. Keccak returns
    `t0` as bare ownership inside `keccakCallerPost`, `t1`/`t2`/`t3`/`t4` at the
    head of `regOwns keccakCsrsRestNoX5`, and `s0` inside
    `regsAt keccakFrame` — the copy loop needs `s0` at its caller-supplied value
    and the other four merely owned. All of that lines up only because
    `keccakCsrsRestNoX5` begins `[x6, x7, x28, x29]` and `regOwns`/`regsAt` are
    plain right-nested `**` chains, so `regOwns_cons`/`regsAt_cons` atomise them.

    The digest hand-off is the other half: the callee's post gives
    `bytesRegion afp_digest (keccakBodyDigest input 0 64)`, and
    `keccakBodyDigest_eq_specref` turns that into `SpecRef.keccak256 input`, so
    the final window is stated against the SPEC REFERENCE rather than the guest's
    own sponge model. -/

set_option maxRecDepth 100000 in
theorem afp_call_and_copy_spec (sp0 vRa inputBase oPtr : Word)
    (input orig : List (BitVec 8)) (v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8))
    (hinput : input.length = 64) (hos : os.length = 200)
    (hb8i : (keccakAbsorbCursor inputBase 0).toNat % 8 = 0)
    (hoveri : ∀ n, n < 64 →
      (keccakAbsorbCursor inputBase 0).toNat + (64 - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < 64 →
      isValidByteAccess
        (keccakAbsorbCursor inputBase 0 + BitVec.ofNat 64 (64 - (n + 1))) = true)
    (horig : orig.length = 20)
    (hdalign : afpDigestPtr.toNat % 8 = 0) (hoalign : oPtr.toNat % 8 = 0)
    (hdover : afpDigestPtr.toNat + 32 < 2 ^ 64) (hoover : oPtr.toNat + 20 < 2 ^ 64)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (afpDigestPtr + BitVec.ofNat 64 j) = true)
    (hovalid : ∀ j, j < 20 → isValidByteAccess (oPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin ((1 + (5 + keccakBodyFuel 0 64 + 6)) + 185)
        (afpAt afpB 7) (afpAt afpB 20) afpFullCode
      (((.x1 : Reg) ↦ᵣ vRa) ** ((.x2 : Reg) ↦ᵣ sp0) **
        regsAt keccakFrame (keccakEntryVals oPtr v9 v18 v20) **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        keccakCallerPre inputBase (64 : Word) afpDigestPtr
          v28 v29 os input (List.replicate 32 (0 : BitVec 8))
          (bytesRegion oPtr orig))
      (((.x1 : Reg) ↦ᵣ (afpAt afpB 8)) ** ((.x2 : Reg) ↦ᵣ sp0) **
        ((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion afpDigestPtr (EvmAsm.Stateless.SpecRef.keccak256 input) **
        bytesRegion oPtr ((EvmAsm.Stateless.SpecRef.keccak256 input).drop 12) **
        regOwns afpScratch **
        (((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
          frameSlotsSaved keccakFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals oPtr v9 v18 v20) **
          ((.x10 : Reg) ↦ᵣ (0 : Word)) **
          bytesRegion Zk3
            (setBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwns [(.x30 : Reg), .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          bytesRegion (keccakAbsorbCursor inputBase 0) (keccakResidual input 0) **
          bytesRegion inputBase (input.take (keccakAbsorbStep * 0)))) := by
  -- The digest the callee leaves IS the reference keccak256 of the input.
  have hdigest : keccakBodyDigest input 0 64
      = EvmAsm.Stateless.SpecRef.keccak256 input := by
    refine keccakBodyDigest_eq_specref input 0 64 ?_ (by decide)
    rw [hinput]; decide
  have hdigLen : (EvmAsm.Stateless.SpecRef.keccak256 input).length = 32 :=
    EvmAsm.Stateless.SpecRef.keccak256_length input
  have hcall := afp_keccak_call_spec sp0 vRa inputBase input oPtr v9 v18 v20 v28 v29
    os (bytesRegion oPtr orig) (bytesRegion_pcFree _ _) hinput hos hb8i hoveri hvalidi
  have hafter := afp_after_keccak_own oPtr (EvmAsm.Stateless.SpecRef.keccak256 input)
    orig hdigLen horig hdalign hoalign hdover hoover hdvalid hovalid
  -- Everything the copy loop does not touch, framed across it.
  have hafterF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ (afpAt afpB 8)) ** ((.x2 : Reg) ↦ᵣ sp0) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
      frameSlotsSaved keccakFrame (sp0 + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals oPtr v9 v18 v20) **
      ((.x10 : Reg) ↦ᵣ (0 : Word)) **
      bytesRegion Zk3
        (setBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwns [(.x30 : Reg), .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
      bytesRegion (keccakAbsorbCursor inputBase 0) (keccakResidual input 0) **
      bytesRegion inputBase (input.take (keccakAbsorbStep * 0)))
    (by
      refine pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj ?_
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj (bytesRegion_pcFree _ _)
        (pcFree_sepConj pcFree_regIs (pcFree_sepConj (pcFree_regOwns _)
        (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _)))))))))))
      exact pcFree_frameSlotsSaved _ _ _)
    hafter
  simp only [keccakCallerPost, keccakCallerFreeA, keccakCsrsRestNoX5,
    regOwns_cons, regOwns_nil, regsAt_cons, regsAt_nil, keccakFrame,
    keccakEntryVals, afpScratch, sepConj_emp_right'] at hcall hafterF ⊢
  rw [hdigest] at hcall
  have hcomb := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hcall hafterF
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) hcomb


/-! ## Increment 3h (#12224): the whole body, indices 3-21

    Setup, keccak call, digest copy, and the `li a0, 0` return value — the entire
    `afpBody`, which is exactly what `abiFrame_spec_own` takes as its `hbody`.

    The precondition is written ATOMISED rather than as `keccakCallerPre`, because
    the setup runs BEFORE the callee's contract applies: on entry `a1` still holds
    the caller's output pointer and `a2` is arbitrary, and it is the setup that
    turns them into keccak's length and output arguments. Folding them into
    `keccakCallerPre` would misstate the entry condition. -/

set_option maxRecDepth 100000 in
theorem afp_body_spec (sp0 vRa inputBase oPtr : Word)
    (input orig : List (BitVec 8)) (v8 v9 v12 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8))
    (hinput : input.length = 64) (hos : os.length = 200)
    (hb8i : (keccakAbsorbCursor inputBase 0).toNat % 8 = 0)
    (hoveri : ∀ n, n < 64 →
      (keccakAbsorbCursor inputBase 0).toNat + (64 - (n + 1)) < 2 ^ 64)
    (hvalidi : ∀ n, n < 64 →
      isValidByteAccess
        (keccakAbsorbCursor inputBase 0 + BitVec.ofNat 64 (64 - (n + 1))) = true)
    (horig : orig.length = 20)
    (hdalign : afpDigestPtr.toNat % 8 = 0) (hoalign : oPtr.toNat % 8 = 0)
    (hdover : afpDigestPtr.toNat + 32 < 2 ^ 64) (hoover : oPtr.toNat + 20 < 2 ^ 64)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (afpDigestPtr + BitVec.ofNat 64 j) = true)
    (hovalid : ∀ j, j < 20 → isValidByteAccess (oPtr + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (4 + ((1 + (5 + keccakBodyFuel 0 64 + 6)) + 185) + 1)
        (afpAt afpB 3) (afpAt afpB 21) afpFullCode
      (((.x1 : Reg) ↦ᵣ vRa) ** ((.x2 : Reg) ↦ᵣ sp0) **
        ((.x8 : Reg) ↦ᵣ v8) ** ((.x11 : Reg) ↦ᵣ oPtr) ** ((.x12 : Reg) ↦ᵣ v12) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        ((.x10 : Reg) ↦ᵣ inputBase) ** ((.x28 : Reg) ↦ᵣ v28) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion Zk3 os **
        bytesRegion inputBase input **
        bytesRegion afpDigestPtr (List.replicate 32 (0 : BitVec 8)) **
        bytesRegion oPtr orig)
      (((.x1 : Reg) ↦ᵣ (afpAt afpB 8)) ** ((.x2 : Reg) ↦ᵣ sp0) **
        ((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
        ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ((.x8 : Reg) ↦ᵣ oPtr) **
        bytesRegion afpDigestPtr (EvmAsm.Stateless.SpecRef.keccak256 input) **
        bytesRegion oPtr ((EvmAsm.Stateless.SpecRef.keccak256 input).drop 12) **
        regOwns afpScratch **
        (((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
          frameSlotsSaved keccakFrame (sp0 + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals oPtr v9 v18 v20) **
          bytesRegion Zk3
            (setBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0)) **
          ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          regOwns [(.x30 : Reg), .x31, .x11, .x12, .x13, .x14, .x15, .x16, .x17] **
          bytesRegion (keccakAbsorbCursor inputBase 0) (keccakResidual input 0) **
          bytesRegion inputBase (input.take (keccakAbsorbStep * 0)))) := by
  -- Setup (3-6), lifted to the union code.
  have hsetup := cpsTripleWithin_extend_code afp_wrapper_mem
    (afp_call_setup_spec oPtr v8 v12
      (((.x1 : Reg) ↦ᵣ vRa) ** ((.x2 : Reg) ↦ᵣ sp0) **
        ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
        frameSlotsOwn keccakFrame (sp0 + signExtend12 (-32 : BitVec 12)) **
        ((.x10 : Reg) ↦ᵣ inputBase) ** ((.x28 : Reg) ↦ᵣ v28) **
        ((.x29 : Reg) ↦ᵣ v29) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns keccakBodyFreeTemps **
        bytesRegion Zk3 os **
        bytesRegion inputBase input **
        bytesRegion afpDigestPtr (List.replicate 32 (0 : BitVec 8)) **
        bytesRegion oPtr orig)
      (by
        refine pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj (pcFree_frameSlotsOwn _ _)
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
          (pcFree_sepConj (pcFree_regOwns _)
          (pcFree_sepConj (bytesRegion_pcFree _ _)
          (pcFree_sepConj (bytesRegion_pcFree _ _)
          (pcFree_sepConj (bytesRegion_pcFree _ _)
            (bytesRegion_pcFree _ _))))))))))))))))
  -- The call and the copy (7-20).
  have hjoin := afp_call_and_copy_spec sp0 vRa inputBase oPtr input orig
    v9 v18 v20 v28 v29 os hinput hos hb8i hoveri hvalidi horig
    hdalign hoalign hdover hoover hdvalid hovalid
  -- `li a0, 0` (20), the routine's return value.
  have hli := cpsTripleWithin_extend_code afp_wrapper_mem
    (cpsTripleWithin_extend_code
      (afpMem afpB 20 (.LI .x10 (0 : Word)) (by decide) rfl)
      (li_spec_gen_within .x10 (0 : Word) (0 : Word) (afpAt afpB 20) (by decide)))
  rw [afpAt_succ afpB 20] at hli
  simp only [keccakCallerPre, regOwns_cons, regOwns_nil, regsAt_cons, regsAt_nil,
    keccakFrame, keccakEntryVals, afpScratch, keccakBodyFreeTemps,
    sepConj_emp_right'] at hsetup hjoin ⊢
  have c1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) hsetup hjoin
  have hliF := cpsTripleWithin_frameR
    (((.x2 : Reg) ↦ᵣ sp0) ** ((.x1 : Reg) ↦ᵣ (afpAt afpB 8)) **
      ((.x5 : Reg) ↦ᵣ afpDigestPtr) ** ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 20) **
      ((.x7 : Reg) ↦ᵣ (20 : Word)) ** ((.x8 : Reg) ↦ᵣ oPtr) **
      bytesRegion afpDigestPtr (EvmAsm.Stateless.SpecRef.keccak256 input) **
      bytesRegion oPtr ((EvmAsm.Stateless.SpecRef.keccak256 input).drop 12) **
      regOwn (.x28 : Reg) ** regOwn (.x29 : Reg) **
      ((.x9 : Reg) ↦ᵣ v9) ** ((.x18 : Reg) ↦ᵣ v18) ** ((.x20 : Reg) ↦ᵣ v20) **
      frameSlotsSaved keccakFrame (sp0 + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals oPtr v9 v18 v20) **
      bytesRegion Zk3
        (setBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0
          (keccakBytes (keccakGuestPad (keccakBodyPrePad input 0 64) 64) 0)) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      regOwn (.x30 : Reg) ** regOwn (.x31 : Reg) ** regOwn (.x11 : Reg) **
      regOwn (.x12 : Reg) ** regOwn (.x13 : Reg) ** regOwn (.x14 : Reg) **
      regOwn (.x15 : Reg) ** regOwn (.x16 : Reg) ** regOwn (.x17 : Reg) **
      bytesRegion (keccakAbsorbCursor inputBase 0) (keccakResidual input 0) **
      bytesRegion inputBase (input.take (keccakAbsorbStep * 0)))
    (by pcFree)
    hli
  have c2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xcancel_struct hp) c1 hliF
  exact cpsTripleWithin_weaken (fun _ hp => by xcancel_struct hp)
    (fun _ hq => by xcancel_struct hq) c2

end EvmAsm.Codegen.AddressFromPubkeySpec
