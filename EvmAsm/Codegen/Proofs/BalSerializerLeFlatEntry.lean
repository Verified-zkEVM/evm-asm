/-
  EvmAsm.Codegen.Proofs.BalSerializerLeFlatEntry

  Flat whole-routine contracts for the two BAL little-endian serializer
  twins at their guest addresses (#12988 tranche 2): the shared
  13-instruction routine (`la` scratch pointer via AUIPC/ADDI, a
  32-iteration reverse byte copy, ret) proved ONCE over a parametric
  base/destination with the `la` identity as a hypothesis, then
  instantiated at both placements (`bal_serializer_slot_to_le`,
  `bal_serializer_balance_to_le`) where the identity closes by `decide`.

  Why the flat layer: the structured contracts (`slotToLeFn_spec`,
  `balanceToLeFn_spec` — `Fn.SpecR`, forced by `blockA`) cannot be
  ret-adapted generically because `asrtR = asrtM ** regOwn x1` FORGETS
  `ra`'s value (see #12988's issue log); the routine itself is small
  enough that the direct flat proof — `countdownLoop_spec` over the
  region-level byte lemmas, the `afpCopyLoop_spec` recipe — is cheaper
  than a pinned-`ra` re-walk of `Stmt.soundR`.  The window laws
  (`revWin`/`revByte`) are reused from `SwrRevLeBeSAsm`.
-/

import EvmAsm.Codegen.Programs.BalSerializerLeSAsm
import EvmAsm.Codegen.Programs.BalSerializer
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.SAsm.AbiFrameLoop
import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.DualReadByteScan
import EvmAsm.Rv64.SAsm.MultiDword
import EvmAsm.Rv64.MemRegion
import EvmAsm.Rv64.MemRegionStore
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.XPerm

namespace EvmAsm.Codegen.BalSerializerLeFlatEntry

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.Tactics
open EvmAsm.Codegen.SwrRevLeBeSAsm (revByte revWin revWin_zero length_revWin
  revWin_step revWin_len_eq)

/-- The shared serializer body, parameterized by the `la` immediates. -/
def bslFlatProg (hi : BitVec 20) (lo : BitVec 12) : List Instr :=
  [ .AUIPC .x5 hi,
    .ADDI .x5 .x5 lo,
    .LI .x6 (32 : Word),
    .ADDI .x7 .x10 (31 : BitVec 12),
    .BEQ .x6 .x0 (28 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

-- The two deployed programs ARE this shape at their immediates.
theorem bslFlatProg_slot :
    bslFlatProg
        (laHi GuestAddrs.bal_serializer_slot_le
          (GuestAddrs.bal_serializer_slot_to_le + 0))
        (laLo GuestAddrs.bal_serializer_slot_le
          (GuestAddrs.bal_serializer_slot_to_le + 0))
      = (balSerializerSlotToLe_prog : List Instr) := rfl

theorem bslFlatProg_balance :
    bslFlatProg
        (laHi GuestAddrs.bal_serializer_balance_le
          (GuestAddrs.bal_serializer_balance_to_le + 0))
        (laLo GuestAddrs.bal_serializer_balance_le
          (GuestAddrs.bal_serializer_balance_to_le + 0))
      = (balSerializerBalanceToLe_prog : List Instr) := rfl

private theorem bslFlatProg_len (hi : BitVec 20) (lo : BitVec 12) :
    (bslFlatProg hi lo).length = 12 := rfl

private theorem bsl_mem (hi : BitVec 20) (lo : BitVec 12) (B : Word)
    (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < 12)
    (hins : (bslFlatProg hi lo)[k]'(by rw [bslFlatProg_len]; omega) = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg B (bslFlatProg hi lo) a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A (bslFlatProg hi lo) k ins hA
      (by rw [bslFlatProg_len]; omega) hins
      (by rw [bslFlatProg_len]; norm_num) a i h

/-- The exposed scratch registers of the serializer. -/
def bslScratch : List Reg := [.x5, .x6, .x7, .x28]

/-- Loop invariant at remaining count `n` (iterations done: `32 - n`):
    the destination cursor sits after the written prefix, the source
    cursor one past the next byte to read (counting down), and the
    destination window holds the reversed prefix. -/
def bslLoopInv (src dst : Word) (bs orig : List (BitVec 8)) (n : Nat) :
    Assertion :=
  ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (32 - n))) **
    ((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 n - 1)) **
    regOwn .x28 **
    bytesRegion src bs **
    bytesRegion dst (revWin bs 32 orig (32 - n))

private theorem bslLoopInv_pcFree (src dst : Word) (bs orig : List (BitVec 8))
    (n : Nat) : (bslLoopInv src dst bs orig n).pcFree := by
  unfold bslLoopInv
  pcFree

set_option maxRecDepth 8000 in
/-- The per-iteration body: read the source byte (counting down), write
    it at the destination cursor, advance all three cursors, jump back to
    the header. -/
private theorem bsl_body_spec (hi : BitVec 20) (lo : BitVec 12)
    (B src dst : Word) (bs orig : List (BitVec 8))
    (hbs : bs.length = 32) (horig : orig.length = 32)
    (hsalign : src.toNat % 8 = 0) (hdalign : dst.toNat % 8 = 0)
    (hsover : src.toNat + 32 < 2 ^ 64) (hdover : dst.toNat + 32 < 2 ^ 64)
    (hsvalid : ∀ j, j < 32 →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true)
    (n : Nat) (hn : n < 32) :
    cpsTripleWithin 6 (B + 20) (B + 16)
      (CodeReq.ofProg B (bslFlatProg hi lo))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bslLoopInv src dst bs orig (n + 1))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bslLoopInv src dst bs orig n) := by
  set i := 31 - n with hidef
  have hi32 : 32 - (n + 1) = i := by omega
  have hi32' : 32 - n = i + 1 := by omega
  have hsrcCur : src + BitVec.ofNat 64 (n + 1) - 1 = src + BitVec.ofNat 64 n := by
    bv_omega
  have hwinlen : (revWin bs 32 orig i).length = 32 := by
    rw [length_revWin bs 32 orig i horig (by omega)]
  -- the source byte read this iteration IS the i-th reversed output byte
  have hbyte : (bs[n]'(by omega)) = revByte bs 32 i := by
    show _ = bs.getD (32 - 1 - i) 0
    rw [show (32 - 1 - i : Nat) = n from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  -- Open the owned scratch register at a concrete valuation.
  refine cpsTripleWithin_weaken (fun h hp => by
      show ((((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        (((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (32 - (n + 1)))) **
          ((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 (n + 1) - 1)) **
          bytesRegion src bs **
          bytesRegion dst (revWin bs 32 orig (32 - (n + 1))))) **
        regOwn .x28) h
      unfold bslLoopInv at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_of_forall_regIs_to_regOwn (fun v28 => ?_))
  -- ---- idx 5: lbu x28, 0(x7) ----
  have hlbu := bytesRegion_lbu_within .x28 .x7 src v28 (B + 20) bs n
    (by decide) hsalign (by omega) (by omega) (hsvalid n hn)
  -- ---- idx 6: sb x28, 0(x5) ----
  have hsb := bytesRegion_sb_within .x5 .x28 dst
    ((bs[n]'(by omega)).zeroExtend 64) (B + 24)
    (revWin bs 32 orig i) i hdalign (by omega) (by omega)
    (hdvalid i (by omega))
  rw [show (((bs[n]'(by omega)).zeroExtend 64 : Word)).truncate 8
        = bs[n]'(by omega) from
      truncate_zeroExtend_byte _,
    show (revWin bs 32 orig i).set i (bs[n]'(by omega))
        = revWin bs 32 orig (i + 1) from by
      rw [hbyte, ← setBytes_singleton]
      exact revWin_step bs 32 orig i horig (by omega)] at hsb
  -- ---- idx 7-9: cursor and counter updates ----
  have haddi7 := addi_spec_gen_same_within .x7 (src + BitVec.ofNat 64 n)
    (-1 : BitVec 12) (B + 28) (by decide)
  rw [show signExtend12 (-1 : BitVec 12) = (0xFFFFFFFFFFFFFFFF : Word)
        from by decide,
      show (src + BitVec.ofNat 64 n + (0xFFFFFFFFFFFFFFFF : Word))
          = src + BitVec.ofNat 64 n - 1 from by bv_omega] at haddi7
  have haddi5 := addi_spec_gen_same_within .x5 (dst + BitVec.ofNat 64 i)
    (1 : BitVec 12) (B + 32) (by decide)
  rw [show signExtend12 (1 : BitVec 12) = (1 : Word) from by decide,
      show (dst + BitVec.ofNat 64 i + (1 : Word))
          = dst + BitVec.ofNat 64 (i + 1) from by bv_omega] at haddi5
  have haddi6 := addi_spec_gen_same_within .x6 (BitVec.ofNat 64 (n + 1))
    (-1 : BitVec 12) (B + 36) (by decide)
  rw [show signExtend12 (-1 : BitVec 12) = (0xFFFFFFFFFFFFFFFF : Word)
        from by decide,
      show (BitVec.ofNat 64 (n + 1) + (0xFFFFFFFFFFFFFFFF : Word))
          = BitVec.ofNat 64 n from by bv_omega] at haddi6
  -- ---- idx 10: jal back to the header ----
  have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (B + 40)
  rw [show (B + 40 : Word) + signExtend21 (-24 : BitVec 21) = B + 16 from by
        rw [show signExtend21 (-24 : BitVec 21)
              = (0xFFFFFFFFFFFFFFE8 : Word) from by decide,
          BitVec.add_assoc]
        rfl] at hjal
  -- ---- membership lifts ----
  have hLbu := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 5 _ (B + 20)
      (by rw [show (4 * 5 : Nat) = 20 from rfl]; rfl) (by omega) rfl) hlbu
  rw [show (B + 20 : Word) + 4 = B + 24 from by rw [BitVec.add_assoc]; rfl]
    at hLbu
  have hSb := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 6 _ (B + 24)
      (by rw [show (4 * 6 : Nat) = 24 from rfl]; rfl) (by omega) rfl) hsb
  rw [show (B + 24 : Word) + 4 = B + 28 from by rw [BitVec.add_assoc]; rfl]
    at hSb
  have hA7 := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 7 _ (B + 28)
      (by rw [show (4 * 7 : Nat) = 28 from rfl]; rfl) (by omega) rfl) haddi7
  rw [show (B + 28 : Word) + 4 = B + 32 from by rw [BitVec.add_assoc]; rfl]
    at hA7
  have hA5 := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 8 _ (B + 32)
      (by rw [show (4 * 8 : Nat) = 32 from rfl]; rfl) (by omega) rfl) haddi5
  rw [show (B + 32 : Word) + 4 = B + 36 from by rw [BitVec.add_assoc]; rfl]
    at hA5
  have hA6 := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 9 _ (B + 36)
      (by rw [show (4 * 9 : Nat) = 36 from rfl]; rfl) (by omega) rfl) haddi6
  rw [show (B + 36 : Word) + 4 = B + 40 from by rw [BitVec.add_assoc]; rfl]
    at hA6
  have hJal := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 10 _ (B + 40)
      (by rw [show (4 * 10 : Nat) = 40 from rfl]; rfl) (by omega) rfl) hjal
  -- ---- fuse the six steps ----
  have hMid : cpsTripleWithin 6 (B + 20) (B + 16)
      (CodeReq.ofProg B (bslFlatProg hi lo))
      (((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 n)) ** ((.x28 : Reg) ↦ᵣ v28) **
        bytesRegion src bs **
        ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 i)) **
        bytesRegion dst (revWin bs 32 orig i) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 (n + 1)))
      (((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 n - 1)) **
        ((.x28 : Reg) ↦ᵣ ((bs[n]'(by omega)).zeroExtend 64)) **
        bytesRegion src bs **
        ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
        bytesRegion dst (revWin bs 32 orig (i + 1)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n)) := by
    runBlock hLbu hSb hA7 hA5 hA6 hJal
  have hMidF := cpsTripleWithin_frameR ((.x0 : Reg) ↦ᵣ (0 : Word))
    (by pcFree) hMid
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hMidF
  · rw [show (32 - (n + 1) : Nat) = i from hi32,
      show src + BitVec.ofNat 64 (n + 1) - 1 = src + BitVec.ofNat 64 n
        from hsrcCur] at hp
    xperm_hyp hp
  · show (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bslLoopInv src dst bs orig n) h
    unfold bslLoopInv
    rw [show (32 - n : Nat) = i + 1 from hi32']
    have hq1 : (((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 n - 1)) **
        regOwn .x28 **
        bytesRegion src bs **
        ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 (i + 1))) **
        bytesRegion dst (revWin bs 32 orig (i + 1)) **
        ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 n) **
        ((.x0 : Reg) ↦ᵣ (0 : Word))) h := by
      have hq0 := sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (regIs_implies_regOwn .x28))) h hq
      xperm_hyp hq0
    xperm_hyp hq1

/-- The whole reverse-copy loop, as a `countdownLoop_spec` instance. -/
private theorem bsl_loop_spec (hi : BitVec 20) (lo : BitVec 12)
    (B src dst : Word) (bs orig : List (BitVec 8))
    (hbs : bs.length = 32) (horig : orig.length = 32)
    (hsalign : src.toNat % 8 = 0) (hdalign : dst.toNat % 8 = 0)
    (hsover : src.toNat + 32 < 2 ^ 64) (hdover : dst.toNat + 32 < 2 ^ 64)
    (hsvalid : ∀ j, j < 32 →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (32 * (6 + 1) + 1) (B + 16) (B + 44)
      (CodeReq.ofProg B (bslFlatProg hi lo))
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 32) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bslLoopInv src dst bs orig 32)
      (((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bslLoopInv src dst bs orig 0) :=
  countdownLoop_spec (CodeReq.ofProg B (bslFlatProg hi lo)) (B + 16) (B + 44)
    .x6 (28 : BitVec 13) 6 32 (bslLoopInv src dst bs orig)
    (by decide) (by norm_num)
    (by
      rw [show signExtend13 (28 : BitVec 13) = (28 : Word) from by decide,
        BitVec.add_assoc]
      rfl)
    (bslLoopInv_pcFree src dst bs orig)
    (bsl_mem hi lo B 4 _ (B + 16)
      (by rw [show (4 * 4 : Nat) = 16 from rfl]; rfl) (by omega) rfl)
    (fun n hn => by
      rw [show (B + 16 : Word) + 4 = B + 20 from by
        rw [BitVec.add_assoc]; rfl]
      exact bsl_body_spec hi lo B src dst bs orig hbs horig
        hsalign hdalign hsover hdover hsvalid hdvalid n hn)

set_option maxRecDepth 8000 in
/-- **The serializer, parametric over its placement**: entered at `B` with
    a 32-byte source at `a0` and the `la` identity tying the AUIPC/ADDI
    pair to the destination scratch `dst`, it returns with the scratch
    holding the REVERSED source bytes (BE → LE) and the source intact. -/
theorem bslFlat_spec (hi : BitVec 20) (lo : BitVec 12)
    (B src dst ret : Word) (bs orig : List (BitVec 8))
    (hla : B + (((hi.zeroExtend 32 : BitVec 32)) <<< 12).signExtend 64
        + signExtend12 lo = dst)
    (hbs : bs.length = 32) (horig : orig.length = 32)
    (hsalign : src.toNat % 8 = 0) (hdalign : dst.toNat % 8 = 0)
    (hsover : src.toNat + 32 < 2 ^ 64) (hdover : dst.toNat + 32 < 2 ^ 64)
    (hsvalid : ∀ j, j < 32 →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (hdvalid : ∀ j, j < 32 →
      isValidByteAccess (dst + BitVec.ofNat 64 j) = true)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (4 + (32 * (6 + 1) + 1) + 1) B (ret &&& ~~~1)
      (CodeReq.ofProg B (bslFlatProg hi lo))
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns bslScratch **
        bytesRegion src bs ** bytesRegion dst orig)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwns bslScratch **
        bytesRegion src bs ** bytesRegion dst (bs.take 32).reverse) := by
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns bslScratch (by decide)
      (P := ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        bytesRegion src bs ** bytesRegion dst orig)
      (fun vf => ?_))
  
  -- ---- idx 0-3: la (AUIPC/ADDI), counter, source cursor ----
  have hauipc := auipc_spec_gen_within .x5 (vf .x5) hi B (by decide)
  have haddilo := addi_spec_gen_same_within .x5
    (B + ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64) lo (B + 4)
    (by decide)
  rw [hla] at haddilo
  rw [show (B + 4 : Word) + 4 = B + 8 from by bv_omega]
    at haddilo
  have hli := li_spec_gen_within .x6 (vf .x6) (32 : Word) (B + 8) (by decide)
  rw [show (B + 8 : Word) + 4 = B + 12 from by bv_omega]
    at hli
  have haddi31 := addi_spec_gen_within .x7 .x10 (vf .x7) src (31 : BitVec 12)
    (B + 12) (by decide)
  rw [show signExtend12 (31 : BitVec 12) = (31 : Word) from by decide,
      show (B + 12 : Word) + 4 = B + 16 from by bv_omega]
    at haddi31
  have hAuipc := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 0 _ B
      (by rw [show (4 * 0 : Nat) = 0 from rfl]; bv_omega) (by omega) rfl)
    hauipc
  have hAddilo := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 1 _ (B + 4)
      (by rw [show (4 * 1 : Nat) = 4 from rfl]; rfl) (by omega) rfl)
    haddilo
  have hLi := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 2 _ (B + 8)
      (by rw [show (4 * 2 : Nat) = 8 from rfl]; rfl) (by omega) rfl)
    hli
  have hAddi31 := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 3 _ (B + 12)
      (by rw [show (4 * 3 : Nat) = 12 from rfl]; rfl) (by omega) rfl)
    haddi31
  have hAuipcF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x10 : Reg) ↦ᵣ src) **
      ((.x7 : Reg) ↦ᵣ vf .x7)) (by pcFree) hAuipc
  have hAddiloF := cpsTripleWithin_frameR
    (((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x10 : Reg) ↦ᵣ src) **
      ((.x7 : Reg) ↦ᵣ vf .x7)) (by pcFree) hAddilo
  have hLiF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ dst) ** ((.x10 : Reg) ↦ᵣ src) **
      ((.x7 : Reg) ↦ᵣ vf .x7)) (by pcFree) hLi
  have hAddi31F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ dst) ** ((.x6 : Reg) ↦ᵣ (32 : Word))) (by pcFree) hAddi31
  have p1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hAuipcF hAddiloF
    intro h hp; xperm_hyp hp
  have p2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ p1 hLiF
    intro h hp; xperm_hyp hp
  have hProl := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ p2 hAddi31F
    intro h hp; xperm_hyp hp
  -- ---- the loop ----
  have hLoop := bsl_loop_spec hi lo B src dst bs orig hbs horig
    hsalign hdalign hsover hdover hsvalid hdvalid
  -- ---- idx 11: ret ----
  have hret := jalr_x0_spec_gen_within .x1 ret (0 : BitVec 12) (B + 44)
  rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
      show (ret + 0 : Word) = ret from by bv_omega] at hret
  have hRet := cpsTripleWithin_extend_code
    (bsl_mem hi lo B 11 _ (B + 44)
      (by rw [show (4 * 11 : Nat) = 44 from rfl]; rfl) (by omega) rfl) hret
  -- ---- frame, reshape, compose ----
  have hProlF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ vf .x28) **
      bytesRegion src bs ** bytesRegion dst orig)
    (by pcFree) hProl
  have hLoopF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src))
    (by pcFree) hLoop
  have hRetF := cpsTripleWithin_frameR
    (((.x10 : Reg) ↦ᵣ src) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 32)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
      ((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 0 - 1)) **
      regOwn .x28 **
      bytesRegion src bs **
      bytesRegion dst (revWin bs 32 orig 32))
    (by pcFree) hRet
  have s1 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ hProlF hLoopF
    intro h hp
    show ((((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 32) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) ** bslLoopInv src dst bs orig 32) **
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src))) h
    unfold bslLoopInv
    rw [show (32 - 32 : Nat) = 0 from rfl, revWin_zero,
      show (BitVec.ofNat 64 0) = (0 : Word) from rfl,
      show dst + (0 : Word) = dst from by bv_omega,
      show src + BitVec.ofNat 64 32 - 1 = src + (31 : Word) from by bv_omega,
      show (BitVec.ofNat 64 32) = (32 : Word) from rfl]
    have hpA : ((((.x28 : Reg) ↦ᵣ vf .x28)) **
        (((.x6 : Reg) ↦ᵣ (32 : Word)) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x5 : Reg) ↦ᵣ dst) ** ((.x7 : Reg) ↦ᵣ (src + (31 : Word))) **
          bytesRegion src bs ** bytesRegion dst orig **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src))) h := by
      xperm_hyp hp
    have hpB := sepConj_mono_left (regIs_implies_regOwn .x28) h hpA
    xperm_hyp hpB
  have s2 := by
    refine cpsTripleWithin_seq_perm_same_cr ?_ s1 hRetF
    intro h hp
    unfold bslLoopInv at hp
    xperm_hyp hp
  refine cpsTripleWithin_weaken (fun h hp => by
      simp only [bslScratch, regAtomsOf_cons, regAtomsOf_nil,
        sepConj_emp_right'] at hp
      xperm_hyp hp)
    (fun h hq => ?_) s2
  show (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
    ((.x0 : Reg) ↦ᵣ (0 : Word)) **
    regOwns bslScratch **
    bytesRegion src bs ** bytesRegion dst (bs.take 32).reverse) h
  rw [show regOwns bslScratch
      = (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28) from by
    simp only [bslScratch, regOwns_cons, regOwns_nil, sepConj_emp_right'],
    show (bs.take 32).reverse = revWin bs 32 orig 32 from
      (revWin_len_eq bs 32 orig horig (by omega)).symm]
  have hqA : (((((.x5 : Reg) ↦ᵣ (dst + BitVec.ofNat 64 32)) **
      ((.x6 : Reg) ↦ᵣ BitVec.ofNat 64 0) **
      ((.x7 : Reg) ↦ᵣ (src + BitVec.ofNat 64 0 - 1)))) **
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwn .x28 **
        bytesRegion src bs ** bytesRegion dst (revWin bs 32 orig 32))) h := by
    xperm_hyp hq
  have hqB := sepConj_mono_left
    (sepConj_mono (regIs_implies_regOwn .x5)
      (sepConj_mono (regIs_implies_regOwn .x6)
        (regIs_implies_regOwn .x7))) h hqA
  xperm_hyp hqB

/-! ## The two guest placements -/

/-- **`bal_serializer_slot_to_le` at its linked guest address**: the
    32-byte `bal_serializer_slot_le` scratch ends as the reversed
    (BE → LE) source bytes; the source is intact. -/
theorem balSerializerSlotToLeFlat_spec (src ret : Word)
    (bs orig : List (BitVec 8))
    (hbs : bs.length = 32) (horig : orig.length = 32)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + 32 < 2 ^ 64)
    (hsvalid : ∀ j, j < 32 →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (4 + (32 * (6 + 1) + 1) + 1)
      (GuestAddrs.bal_serializer_slot_to_le : Word) (ret &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.bal_serializer_slot_to_le : Word)
        balSerializerSlotToLe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns bslScratch **
        bytesRegion src bs **
        bytesRegion (GuestAddrs.bal_serializer_slot_le : Word) orig)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns bslScratch **
        bytesRegion src bs **
        bytesRegion (GuestAddrs.bal_serializer_slot_le : Word)
          (bs.take 32).reverse) := by
  have h := bslFlat_spec
    (laHi GuestAddrs.bal_serializer_slot_le
      (GuestAddrs.bal_serializer_slot_to_le + 0))
    (laLo GuestAddrs.bal_serializer_slot_le
      (GuestAddrs.bal_serializer_slot_to_le + 0))
    (GuestAddrs.bal_serializer_slot_to_le : Word) src
    (GuestAddrs.bal_serializer_slot_le : Word) ret bs orig
    rfl hbs horig hsalign (by decide) hsover (by decide)
    hsvalid (fun j hj => by
      revert hj
      revert j
      decide)
    halign
  rwa [bslFlatProg_slot] at h

/-- **`bal_serializer_balance_to_le` at its linked guest address**. -/
theorem balSerializerBalanceToLeFlat_spec (src ret : Word)
    (bs orig : List (BitVec 8))
    (hbs : bs.length = 32) (horig : orig.length = 32)
    (hsalign : src.toNat % 8 = 0) (hsover : src.toNat + 32 < 2 ^ 64)
    (hsvalid : ∀ j, j < 32 →
      isValidByteAccess (src + BitVec.ofNat 64 j) = true)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (4 + (32 * (6 + 1) + 1) + 1)
      (GuestAddrs.bal_serializer_balance_to_le : Word) (ret &&& ~~~1)
      (CodeReq.ofProg (GuestAddrs.bal_serializer_balance_to_le : Word)
        balSerializerBalanceToLe_prog)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns bslScratch **
        bytesRegion src bs **
        bytesRegion (GuestAddrs.bal_serializer_balance_le : Word) orig)
      (((.x1 : Reg) ↦ᵣ ret) ** ((.x10 : Reg) ↦ᵣ src) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)) ** regOwns bslScratch **
        bytesRegion src bs **
        bytesRegion (GuestAddrs.bal_serializer_balance_le : Word)
          (bs.take 32).reverse) := by
  have h := bslFlat_spec
    (laHi GuestAddrs.bal_serializer_balance_le
      (GuestAddrs.bal_serializer_balance_to_le + 0))
    (laLo GuestAddrs.bal_serializer_balance_le
      (GuestAddrs.bal_serializer_balance_to_le + 0))
    (GuestAddrs.bal_serializer_balance_to_le : Word) src
    (GuestAddrs.bal_serializer_balance_le : Word) ret bs orig
    rfl hbs horig hsalign (by decide) hsover (by decide)
    hsvalid (fun j hj => by
      revert hj
      revert j
      decide)
    halign
  rwa [bslFlatProg_balance] at h

end EvmAsm.Codegen.BalSerializerLeFlatEntry
