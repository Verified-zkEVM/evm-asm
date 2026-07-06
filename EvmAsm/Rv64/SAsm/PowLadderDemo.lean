/-
  EvmAsm.Rv64.SAsm.PowLadderDemo

  The crypto-kernel pilot (bead evm-asm-4ch8f.11, strategy in
  docs/4ch8f-crypto-strategy.md): an MSB-first square-and-multiply modular
  exponentiation ladder whose every multiply is the ZisK Arith256Mod
  accelerator (`csrs 0x802`), proven to leave `x ^ e mod m` in the output
  buffer — the number-theoretic spec `EvmAsm.Crypto.ladder_correct`
  composed with the machine-level accelerator handle
  (`SAsm.arith256ModHandle`, AccelStep.lean).

  This is the exact composition the real crypto kernels need
  (`p256_pow`, `secf_pow_mod_p/n`, `bnq_pow`, `blq_pow`, `blm_fp_pow`,
  `zkvm_modexp`): a loop over exponent bits read MSB-first from a
  read-only constant, each iteration squaring the accumulator through the
  `{a,b,c,module,d}` parameter-block wrapper and conditionally multiplying
  by the base, with the accumulator/param staging in one writable arena.

  What it exercises, mapped to the strategy's risk list:
  - CSRS-step semantics reached through `Stmt.callRegS` from inside a
    loop (the SAsm block engine never sees the `CSRS`);
  - the param-block convention under *aliasing* (`a = b = d = acc` for
    the square; `a = d = acc` for the multiply);
  - a nontrivial number-theoretic postcondition (`x ^ e mod m` over
    `Nat.pow` — not a shape a wrong ladder satisfies; see the kernel KATs
    in EvmAsm/Crypto/PowLadder.lean);
  - a symbolic exponent width (fuel `8 * ebytes.length`, closing the
    cap-VC for any byte length up to 4096 — covering the 254/256/384-bit
    Fermat exponents and the 3044/4569-bit pairing final-exp constants);
  - the `1 < m` precondition is load-bearing: at `m = 1` the unreduced
    `acc₀ = 1` staging breaks the invariant at entry — exactly the
    MODEXP `modulus == 1` corner of bead evm-asm-4ch8f.11.5.

  Like the `.10` pilot (InterpLoopDemo), all addresses are demo-local
  constants — nothing depends on `GuestAddrs` (which bead .9.5 is
  relaying), and the real per-kernel beads re-instantiate the same
  handle/ladder shapes at linked addresses.
-/

import EvmAsm.Rv64.SAsm.AccelStep
import EvmAsm.Rv64.SAsm.RaSpill
import EvmAsm.Rv64.SAsm.LoopFuel
import EvmAsm.Rv64.SAsm.Tactic
import EvmAsm.Crypto.PowLadder

namespace EvmAsm.Rv64
namespace SAsm
namespace PowLadderDemo

set_option linter.unusedSimpArgs false

open Stmt

-- The pilot's window-locality lemmas (`wsDword_setBytes_low`,
-- `wsNat256_setBytes_low`, `flatMap_dwordBytes_slice`,
-- `wsNat256_setBytes_leBytes32`) were promoted into AccelStep.lean
-- (bead 4ch8f.11.6), generalized to `nl` limbs — this file consumes them
-- from there.

-- ============================================================================
-- The arena layout (demo-local; no GuestAddrs dependence)
-- ============================================================================

/-- Exponent constant's read-only base (legacy valid-memory zone). -/
def powExpBase : Word := 0x10000

/-- Writable arena base (legacy valid-memory zone). -/
def powArena : Word := 0x20000

/-- The Arith256Mod wrapper's entry point. -/
def powWrapperEntry : Word := 0x2000

/-- The ladder function's code base. -/
def powFnBase : Word := 0x1000

/-- Arena layout (byte offsets from `powArena`):
    `0` square param block `[acc,acc,zero,mod,acc]`,
    `40` multiply param block `[acc,x,zero,mod,acc]`,
    `80` the zero addend, `112` the modulus, `144` the base, `176` the
    accumulator — 208 bytes. -/
def powRw : RwRegion := ⟨powArena, 208⟩

def powRegion (ebytes : List (BitVec 8)) : Region := ⟨powExpBase, ebytes⟩

/-- The static staging: both param blocks' pointers, the zero addend, the
    modulus, and the base — everything the ladder loop never writes. -/
def stagingOk (m x : Nat) (ws : List (BitVec 8)) : Prop :=
  wsDword ws 0 = powArena + BitVec.ofNat 64 176
  ∧ wsDword ws 8 = powArena + BitVec.ofNat 64 176
  ∧ wsDword ws 16 = powArena + BitVec.ofNat 64 80
  ∧ wsDword ws 24 = powArena + BitVec.ofNat 64 112
  ∧ wsDword ws 32 = powArena + BitVec.ofNat 64 176
  ∧ wsDword ws 40 = powArena + BitVec.ofNat 64 176
  ∧ wsDword ws 48 = powArena + BitVec.ofNat 64 144
  ∧ wsDword ws 56 = powArena + BitVec.ofNat 64 80
  ∧ wsDword ws 64 = powArena + BitVec.ofNat 64 112
  ∧ wsDword ws 72 = powArena + BitVec.ofNat 64 176
  ∧ wsNat256 ws 80 = 0
  ∧ wsNat256 ws 112 = m
  ∧ wsNat256 ws 144 = x

/-- The staging survives an accumulator write (offset 176). -/
theorem stagingOk_setBytes {m x : Nat} {ws ns : List (BitVec 8)}
    (h : stagingOk m x ws) : stagingOk m x (setBytes ws 176 ns) := by
  obtain ⟨h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, hz, hm, hx⟩ := h
  exact ⟨
    (wsDword_setBytes_low (by omega)).trans h0,
    (wsDword_setBytes_low (by omega)).trans h8,
    (wsDword_setBytes_low (by omega)).trans h16,
    (wsDword_setBytes_low (by omega)).trans h24,
    (wsDword_setBytes_low (by omega)).trans h32,
    (wsDword_setBytes_low (by omega)).trans h40,
    (wsDword_setBytes_low (by omega)).trans h48,
    (wsDword_setBytes_low (by omega)).trans h56,
    (wsDword_setBytes_low (by omega)).trans h64,
    (wsDword_setBytes_low (by omega)).trans h72,
    (wsNat256_setBytes_low (by omega)).trans hz,
    (wsNat256_setBytes_low (by omega)).trans hm,
    (wsNat256_setBytes_low (by omega)).trans hx⟩

-- ============================================================================
-- The two handle instantiations (square / multiply param blocks)
-- ============================================================================

set_option maxRecDepth 4000 in
theorem powRw_wf : powRw.wf := by decide

/-- The square step: `acc := (acc·acc + 0) mod m` through param block 0. -/
def sqHandle (ebytes : List (BitVec 8)) : FnHandleS :=
  arith256ModHandle powWrapperEntry .x5 rfl (powRegion ebytes) powArena 208
    powRw_wf 0 176 176 80 112 176
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The multiply step: `acc := (acc·x + 0) mod m` through param block 40. -/
def mulHandle (ebytes : List (BitVec 8)) : FnHandleS :=
  arith256ModHandle powWrapperEntry .x5 rfl (powRegion ebytes) powArena 208
    powRw_wf 40 176 144 80 112 176
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

-- ============================================================================
-- The ladder function
-- ============================================================================

/-- Exponent-bit fetch: byte `i / 8` of the read-only exponent, shifted so
    MSB-first bit `i` lands at position 7, isolated with mask `0x80`. -/
def fetchInstrs : List Instr :=
  [.SRLI .x6 .x29 3, .LI .x7 powExpBase, .ADD .x7 .x7 .x6,
   .LBU .x31 .x7 0, .ANDI .x6 .x29 7, .SLL .x31 .x31 .x6,
   .ANDI .x31 .x31 128]

/-- The loop invariant: after `i` iterations the accumulator decodes to
    `Crypto.ladder m x ebytes i` and the staging is intact. -/
def ladderInv (m x : Nat) (ebytes : List (BitVec 8)) :
    Nat → RegFile → List (BitVec 8) → Assertion → Prop :=
  fun i rf ws _ =>
    rf.get .x29 = BitVec.ofNat 64 i
    ∧ rf.get .x30 = BitVec.ofNat 64 (8 * ebytes.length)
    ∧ i ≤ 8 * ebytes.length
    ∧ stagingOk m x ws
    ∧ wsNat256 ws 176 = Crypto.ladder m x ebytes i
    ∧ ws.length = 208

/-- One ladder iteration: square through param block 0, fetch the bit,
    conditionally multiply through param block 40, bump the counter. -/
def ladderBody (ebytes : List (BitVec 8)) : Stmt :=
  .block "selSq" [.LI .x5 powArena, .LI .x28 powWrapperEntry] ;;;
  .callRegS "sq" .x28 [sqHandle ebytes] ;;;
  .block "fetch" fetchInstrs ;;;
  .when "bit" (.bne .x31 .x0)
    (.block "selMul" [.LI .x5 (powArena + 40)] ;;;
     .callRegS "mul" .x28 [mulHandle ebytes]) ;;;
  .block "inc" [.ADDI .x29 .x29 1]

/-- The MSB square-and-multiply modular-exponentiation ladder: every
    multiply is the Arith256Mod accelerator, reached through
    `Stmt.callRegS` at the hand-proven handle. -/
def powFn (m x : Nat) (ebytes : List (BitVec 8)) : Fn where
  name := "powmod"
  region := powRegion ebytes
  rw := powRw
  pre := fun _ ws _ =>
    stagingOk m x ws ∧ wsNat256 ws 176 = 1 ∧ ws.length = 208
  post := fun _ ws _ =>
    wsNat256 ws 176 = x ^ Crypto.beBytesToNat ebytes % m
  body :=
    .block "init" [.LI .x29 0, .LI .x30 (BitVec.ofNat 64 (8 * ebytes.length))] ;;;
    .«while» "ladder" (.bltu .x29 .x30) (8 * ebytes.length)
      (ladderInv m x ebytes) (ladderBody ebytes)

/-- The ambient code requirement: the ladder loop plus the wrapper. -/
def powCr (m x : Nat) (ebytes : List (BitVec 8)) : CodeReq :=
  (CodeReq.ofProg powFnBase ((powFn m x ebytes).body.flatten powFnBase)).union
    (sqHandle ebytes).code

-- ============================================================================
-- Execution helpers
-- ============================================================================

/-- The bit test: after shifting the fetched byte left by `i % 8`, mask
    `0x80` is set exactly at the MSB-first exponent bit `i`. -/
theorem sll_bit_test (k : Nat) (hk : k < 8) (b : BitVec 8) :
    ((b.zeroExtend 64 <<< k) &&& (128 : Word) ≠ 0) ↔ b.getLsbD (7 - k) = true := by
  interval_cases k <;> revert b <;> decide

/-- An `LBU` that misses the writable window reads the ro region
    (same as InterpLoopDemo's helper). -/
theorem execInstrRF_lbu_ro (ro : Region) (rwBase : Word) (rf : RegFile)
    (ws : List (BitVec 8)) (rd rs1 : Reg) (ofs : BitVec 12)
    (h : ¬ inRw rwBase ws (rf.get rs1 + signExtend12 ofs) 1) :
    execInstrRF ro rwBase rf ws (.LBU rd rs1 ofs)
      = (rf.set rd
          ((ro.byteAt (rf.get rs1 + signExtend12 ofs)).zeroExtend 64), ws) := by
  unfold execInstrRF
  dsimp only [aluSem, loadSem]
  rw [if_neg h]

theorem se12_zero : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
theorem se12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
theorem se12_seven : signExtend12 (7 : BitVec 12) = (7 : Word) := by decide
theorem se12_c128 : signExtend12 (128 : BitVec 12) = (128 : Word) := by decide

/-- Low-3-bit mask on a `Nat` image. -/
theorem toNat_and_seven (i : Nat) :
    ((BitVec.ofNat 64 i) &&& (7 : Word)).toNat = i % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  show (i % 2 ^ 64) &&& (2 ^ 3 - 1) = i % 8
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Byte-index extraction from the shifted counter. -/
theorem toNat_ushiftRight_three {i : Nat} (hi : i < 2 ^ 64) :
    ((BitVec.ofNat 64 i) >>> (3 : Nat)).toNat = i / 8 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- The exponent-bit fetch block, fully executed. -/
theorem exec_fetch (ebytes : List (BitVec 8)) (rf : RegFile)
    (ws : List (BitVec 8)) (i : Nat) (hws : ws.length = 208)
    (hlen : ebytes.length ≤ 4096)
    (hx29 : rf.get .x29 = BitVec.ofNat 64 i) (hi : i < 8 * ebytes.length) :
    execBlock (powRegion ebytes) powArena rf ws fetchInstrs
      = ((((((((rf.set .x6 (BitVec.ofNat 64 i >>> (3 : Nat))).set .x7
            powExpBase).set .x7 (powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)))).set .x31
            ((ebytes.getD (i / 8) 0).zeroExtend 64)).set .x6
            (BitVec.ofNat 64 i &&& 7)).set .x31
            ((ebytes.getD (i / 8) 0).zeroExtend 64 <<< (i % 8))).set .x31
            ((((ebytes.getD (i / 8) 0).zeroExtend 64) <<< (i % 8)) &&& 128)), ws) := by
  have hi64 : i < 2 ^ 64 := by omega
  have haddr7 : ((((rf.set .x6 (BitVec.ofNat 64 i >>> (3 : Nat))).set .x7
        powExpBase).set .x7 (powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)))).get .x7
        + signExtend12 (0 : BitVec 12))
      = powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)) := by
    rw [RegFile.get_set_self _ _ _ (by decide), se12_zero]
    bv_omega
  have hsh : ((BitVec.ofNat 64 i >>> (3 : Nat))).toNat = i / 8 :=
    toNat_ushiftRight_three hi64
  have hnorw : ¬ inRw powArena ws
      ((((rf.set .x6 (BitVec.ofNat 64 i >>> (3 : Nat))).set .x7
        powExpBase).set .x7 (powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)))).get .x7
        + signExtend12 (0 : BitVec 12)) 1 := by
    rw [haddr7]
    unfold inRw
    rw [hws]
    simp only [powExpBase, powArena]
    have : (BitVec.ofNat 64 i >>> (3 : Nat)).toNat = i / 8 := hsh
    bv_omega
  dsimp only [fetchInstrs]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [show ((3 : BitVec 6)).toNat = (3 : Nat) from rfl, hx29]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [show (((rf.set .x6 (BitVec.ofNat 64 i >>> (3 : Nat))).set .x7
      powExpBase).get .x7) = powExpBase from
    RegFile.get_set_self _ _ _ (by decide)]
  rw [show (((rf.set .x6 (BitVec.ofNat 64 i >>> (3 : Nat))).set .x7
      powExpBase).get .x6) = BitVec.ofNat 64 i >>> (3 : Nat) from by
    rw [RegFile.get_set_ne _ _ _ _ (by decide),
      RegFile.get_set_self _ _ _ (by decide)]]
  rw [execBlock_cons, execInstrRF_lbu_ro _ _ _ _ _ _ _ hnorw, haddr7]
  rw [show (powRegion ebytes).byteAt (powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)))
      = ebytes.getD (i / 8) 0 from by
    dsimp only [powRegion, Region.byteAt]
    congr 1
    simp only [powExpBase]
    bv_omega]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, se12_seven, se12_c128]
  rw [hx29]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true]
  rw [show ((BitVec.ofNat 64 i &&& (7 : Word)).toNat % 64) = i % 8 from by
    rw [toNat_and_seven]; omega]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
    not_false_eq_true, se12_c128]
  rw [execBlock_nil]

/-- The `selSq` block, executed (projections). -/
theorem exec_selSq_fst (ro : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock ro rwb rf ws [.LI .x5 powArena, .LI .x28 powWrapperEntry]).1
      = (rf.set .x5 powArena).set .x28 powWrapperEntry := rfl

theorem exec_selSq_snd (ro : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock ro rwb rf ws [.LI .x5 powArena, .LI .x28 powWrapperEntry]).2
      = ws := rfl

/-- The `selMul` block, executed (projections). -/
theorem exec_selMul_fst (ro : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock ro rwb rf ws [.LI .x5 (powArena + 40)]).1
      = rf.set .x5 (powArena + 40) := rfl

theorem exec_selMul_snd (ro : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock ro rwb rf ws [.LI .x5 (powArena + 40)]).2 = ws := rfl

/-- The `inc` block, executed (projections). -/
theorem exec_inc_fst (ro : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock ro rwb rf ws [.ADDI .x29 .x29 1]).1
      = rf.set .x29 (rf.get .x29 + signExtend12 1) := rfl

theorem exec_inc_snd (ro : Region) (rwb : Word) (rf : RegFile)
    (ws : List (BitVec 8)) :
    (execBlock ro rwb rf ws [.ADDI .x29 .x29 1]).2 = ws := rfl

/-- Counter bump: `ofNat i + 1 = ofNat (i+1)`. -/
theorem ofNat64_succ (i : Nat) :
    BitVec.ofNat 64 i + (1 : Word) = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [show ((1 : Word)).toNat = 1 from rfl]
  omega

-- ============================================================================
-- The pilot theorem
-- ============================================================================

/-- **The pilot theorem**: the ladder body, with the staged arena and the
    accelerator wrapper in scope, terminates with the accumulator holding
    `x ^ e mod m` where `e` is the big-endian exponent constant — i.e. the
    machine ladder meets `Nat.pow` (via `Crypto.ladder_correct`), with
    every multiplication performed by `Accel.arith256Mod`. -/
theorem powFn_spec (m x : Nat) (ebytes : List (BitVec 8))
    (hm : 1 < m) (hm256 : m < 2 ^ 256)
    (hlen : ebytes.length ≤ 4096)
    (hro : (powRegion ebytes).wf) :
    (powFn m x ebytes).SpecR powFnBase (powCr m x ebytes) := by
  vcgen
  case region => exact ⟨hro, powRw_wf⟩
  case code =>
    intro a i h
    simp only [powCr, CodeReq.union, h]
  case callees =>
    have hhandle : ∀ a i, (sqHandle ebytes).code a = some i →
        powCr m x ebytes a = some i := by
      intro a i h
      obtain ⟨kk, hk, rfl⟩ := ofProg_some_range h
      have hk2 : kk < 2 := hk
      have hP : CodeReq.ofProg powFnBase
          ((powFn m x ebytes).body.flatten powFnBase)
          (powWrapperEntry + BitVec.ofNat 64 (4 * kk)) = none := by
        apply CodeReq.ofProg_none_range
        intro k' hk' heq
        have hk18 : k' < 18 := hk'
        simp only [powWrapperEntry, powFnBase] at heq
        bv_omega
      simp only [powCr, CodeReq.union, hP, h]
    refine ⟨trivial, trivial, ?_, trivial, ⟨trivial, ?_⟩, trivial⟩
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact ⟨hhandle, rfl, rfl⟩
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact ⟨hhandle, rfl, rfl⟩
  case calls =>
    refine ⟨trivial, trivial, ⟨?_, ?_⟩, trivial, ⟨trivial, ⟨?_, ?_⟩⟩, trivial⟩
    · simp only [Stmt.size, fetchInstrs, List.length_cons, List.length_nil]
      decide
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      show powWrapperEntry &&& ~~~(1 : Word) = powWrapperEntry
      decide
    · simp only [Stmt.size, fetchInstrs, List.length_cons, List.length_nil]
      decide
    · intro h hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      show powWrapperEntry &&& ~~~(1 : Word) = powWrapperEntry
      decide
  case powmod.ladder.inv_init =>
    rintro rf' ws' A' ⟨rf, ws, hws, ⟨hstag, hacc, hlen208⟩, rfl, rfl⟩
    dsimp only [ladderInv]
    refine ⟨?_, ?_, by omega, hstag, hacc, hlen208⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_ne _ _ _ _ (by decide),
        RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
  case powmod.ladder.exhausted =>
    rintro rf ws A ⟨hx29, hx30, -, -, -, -⟩
    dsimp only [Cond.holds]
    rw [hx29, hx30]
    simp [BitVec.ult]
  case powmod.ladder.body.sq.pre =>
    rintro rf' ws' A' ⟨rf, ws, hws,
      ⟨⟨i, hif, ⟨hx29, hx30, hile, hstag, hacc, hlen208⟩, hcond⟩, rfl, rfl⟩⟩
    obtain ⟨h0, h8, h16, h24, h32, -, -, -, -, -, -, hm', -⟩ := hstag
    refine ⟨sqHandle ebytes, by simp, ?_, ?_⟩
    · simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      rw [RegFile.get_set_self _ _ _ (by decide)]
      rfl
    · dsimp only [sqHandle, arith256ModHandle, arith256ModPre]
      simp only [execBlock_cons, execBlock_nil, execInstrRF, aluSem]
      refine ⟨?_, h0, h8, h16, h24, h32, ?_⟩
      · rw [RegFile.get_set_ne _ _ _ _ (by decide),
          RegFile.get_set_self _ _ _ (by decide)]
        decide +kernel
      · rw [hm']
        omega
  case powmod.ladder.body.fetch.mem =>
    rintro rf' ws' A' hws'
      ⟨rfSel, ws, A₀,
        ⟨rf, wsIn, hws, ⟨⟨i, hif, ⟨hx29, hx30, hile, hstag, hacc, hlen208⟩,
          hcond⟩, rfl, rfl⟩⟩, h, hmem, hx28, hpre, hpost⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    obtain ⟨hrfeq, hAeq, hwseq⟩ := hpost
    dsimp only [powFn, powRw, powRegion] at hrfeq hwseq ⊢
    rw [exec_selSq_fst] at hrfeq
    generalize hpay : leBytes32 (Accel.arith256Mod (wsNat256 ws 176)
      (wsNat256 ws 176) (wsNat256 ws 80) (wsNat256 ws 112)) = pay at hwseq
    rw [hrfeq, hwseq]
    have hi64 : i < 2 ^ 64 := by omega
    have hsh : ((BitVec.ofNat 64 i) >>> (3 : Nat)).toNat = i / 8 :=
      toNat_ushiftRight_three hi64
    dsimp only [blockVCs, fetchInstrs, loadSem, storeSem, aluSem, execInstrRF,
      Region.loadOk, powRegion]
    simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
      not_false_eq_true, se12_zero, se12_seven, se12_c128]
    rw [show ((3 : BitVec 6)).toNat = (3 : Nat) from rfl, hx29]
    have hnorw : ¬ inRw powArena (setBytes ws 176 pay)
        (powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)) + (0 : Word)) 1 := by
      unfold inRw
      rw [length_setBytes, hlen208]
      simp only [powExpBase, powArena]
      bv_omega
    rw [if_neg hnorw]
    refine ⟨trivial, trivial, trivial, ⟨one_dvd _, ?_⟩, trivial, trivial,
      trivial, trivial⟩
    show ((powExpBase + (BitVec.ofNat 64 i >>> (3 : Nat)) + (0 : Word))
        - powExpBase).toNat + 1 ≤ ebytes.length
    simp only [powExpBase]
    bv_omega
  case powmod.ladder.body.bit.mul.pre =>
    rintro rf' ws' A' ⟨rf3, ws3, hws3,
      ⟨⟨rf2, ws2, hws2,
        ⟨rfSel, ws, A₀,
          ⟨rf, wsIn, hws, ⟨⟨i, hif, ⟨hx29, hx30, hile, hstag, hacc, hlen208⟩,
            hcond⟩, rfl, rfl⟩⟩, h, hmem, hx28, hpreh, hposth⟩,
        heq3a, heq3b⟩, hbne⟩, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    obtain ⟨hrf2, hA2, hws2eq⟩ := hposth
    dsimp only [powFn, powRw] at hrf2 hws2eq heq3a heq3b hws2 ⊢
    rw [exec_selSq_fst] at hrf2
    generalize hpay : leBytes32 (Accel.arith256Mod (wsNat256 ws 176)
      (wsNat256 ws 176) (wsNat256 ws 80) (wsNat256 ws 112)) = pay at hws2eq
    rw [hrf2, hws2eq] at heq3a heq3b
    rw [exec_fetch ebytes _ _ i
      (by rw [length_setBytes]; exact hlen208) hlen
      (by rw [RegFile.get_set_ne _ _ _ _ (by decide),
            RegFile.get_set_ne _ _ _ _ (by decide)]
          exact hx29)
      hif] at heq3a heq3b
    dsimp only at heq3a heq3b
    subst heq3a heq3b
    have hstag2 : stagingOk m x (setBytes ws 176 pay) := by
      rw [← hpay]; exact stagingOk_setBytes hstag
    obtain ⟨-, -, -, -, -, h40, h48, h56, h64, h72, -, hm', -⟩ := hstag2
    refine ⟨mulHandle ebytes, by simp, ?_, ?_⟩
    · rw [exec_selMul_fst]
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rfl
    · dsimp only [mulHandle, arith256ModHandle, arith256ModPre]
      rw [exec_selMul_fst]
      refine ⟨?_, h40, h48, h56, h64, h72, by rw [hm']; omega⟩
      simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq, reduceCtorEq,
        not_false_eq_true]
      rfl
  case powmod.ladder.inv_step =>
    intro i hif rf' ws' A' hsp
    have hi64 : i < 2 ^ 64 := by omega
    obtain ⟨rf5, ws5, hws5, hX, rfl, rfl⟩ := hsp
    rcases hX with ⟨rf4, ws4, A4, ⟨rf3, ws3, hws3,
        ⟨⟨rf2, ws2, hws2,
          ⟨rfSel, ws, A₀,
            ⟨rf, wsIn, hws, ⟨⟨⟨hx29, hx30, hile, hstag, hacc, hlen208⟩,
              hcond⟩, rfl, rfl⟩⟩,
            h, hmem, hx28, hpreh, hposth⟩, heq3a, heq3b⟩,
          hbne⟩, rfl, rfl⟩,
        h', hmem', hx28', hpreh', hposth'⟩
      | ⟨⟨rf2, ws2, hws2,
          ⟨rfSel, ws, A₀,
            ⟨rf, wsIn, hws, ⟨⟨⟨hx29, hx30, hile, hstag, hacc, hlen208⟩,
              hcond⟩, rfl, rfl⟩⟩,
            h, hmem, hx28, hpreh, hposth⟩, heq3a, heq3b⟩,
          hnbne⟩
    -- ── bit set: square, then multiply by the base ──
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem hmem'
      subst hmem
      subst hmem'
      obtain ⟨hrf2, hA4, hws2eq⟩ := hposth
      dsimp only [powFn, powRw] at hrf2 hws2eq heq3a heq3b hws2 hws3 ⊢
      rw [exec_selSq_fst] at hrf2
      generalize hpay : leBytes32 (Accel.arith256Mod (wsNat256 ws 176)
        (wsNat256 ws 176) (wsNat256 ws 80) (wsNat256 ws 112)) = pay at hws2eq
      rw [hrf2, hws2eq] at heq3a heq3b
      rw [exec_fetch ebytes _ _ i
        (by rw [length_setBytes]; exact hlen208) hlen
        (by rw [RegFile.get_set_ne _ _ _ _ (by decide),
              RegFile.get_set_ne _ _ _ _ (by decide)]
            exact hx29)
        hif] at heq3a heq3b
      dsimp only at heq3a heq3b
      subst heq3a heq3b
      obtain ⟨hrf5, hA', hws5eq⟩ := hposth'
      rw [exec_selMul_fst] at hrf5
      generalize hpay2 : leBytes32 (Accel.arith256Mod
        (wsNat256 (setBytes ws 176 pay) 176)
        (wsNat256 (setBytes ws 176 pay) 144)
        (wsNat256 (setBytes ws 176 pay) 80)
        (wsNat256 (setBytes ws 176 pay) 112)) = pay2 at hws5eq
      subst hrf5
      subst hws5eq
      rw [exec_inc_fst]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hz, hmw, hxw⟩ := id hstag
      -- the fetched bit is set
      have hbit : Crypto.beBit ebytes i = true := by
        dsimp only [Cond.holds] at hbne
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true, RegFile.get_x0] at hbne
        exact (sll_bit_test (i % 8) (by omega) (ebytes.getD (i / 8) 0)).mp hbne
      -- decodes of the post-square window
      have hlt_sq : Accel.arith256Mod (wsNat256 ws 176) (wsNat256 ws 176)
          (wsNat256 ws 80) (wsNat256 ws 112) < 2 ^ 256 := by
        show (_ * _ + _) % _ < 2 ^ 256
        rw [hmw]
        exact lt_trans (Nat.mod_lt _ (by omega)) hm256
      have hacc2 : wsNat256 (setBytes ws 176 pay) 176
          = Accel.arith256Mod (wsNat256 ws 176) (wsNat256 ws 176)
            (wsNat256 ws 80) (wsNat256 ws 112) := by
        rw [← hpay]
        exact wsNat256_setBytes_leBytes32 hlt_sq (by omega)
      have hx2 : wsNat256 (setBytes ws 176 pay) 144 = x :=
        (wsNat256_setBytes_low (by omega)).trans hxw
      have hz2 : wsNat256 (setBytes ws 176 pay) 80 = 0 :=
        (wsNat256_setBytes_low (by omega)).trans hz
      have hm2 : wsNat256 (setBytes ws 176 pay) 112 = m :=
        (wsNat256_setBytes_low (by omega)).trans hmw
      have hlt_mul : Accel.arith256Mod (wsNat256 (setBytes ws 176 pay) 176)
          (wsNat256 (setBytes ws 176 pay) 144)
          (wsNat256 (setBytes ws 176 pay) 80)
          (wsNat256 (setBytes ws 176 pay) 112) < 2 ^ 256 := by
        show (_ * _ + _) % _ < 2 ^ 256
        rw [hm2]
        exact lt_trans (Nat.mod_lt _ (by omega)) hm256
      dsimp only [ladderInv]
      refine ⟨?_, ?_, by omega, ?_, ?_, ?_⟩
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true, se12_one]
        rw [hx29, ofNat64_succ]
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true]
        exact hx30
      · exact stagingOk_setBytes (stagingOk_setBytes hstag)
      · rw [← hpay2, wsNat256_setBytes_leBytes32 hlt_mul
          (by rw [length_setBytes]; omega)]
        rw [hacc2, hx2, hz2, hm2]
        rw [show Crypto.ladder m x ebytes (i + 1)
            = Crypto.ladderStep m x (Crypto.ladder m x ebytes i)
              (Crypto.beBit ebytes i) from rfl, hbit, ← hacc]
        show (((wsNat256 ws 176 * wsNat256 ws 176 + wsNat256 ws 80) % wsNat256 ws 112)
            * x + 0) % m = _
        rw [hz, hmw]
        dsimp only [Crypto.ladderStep]
        simp only [if_true]
        rw [Nat.add_zero, Nat.add_zero]
      · rw [length_setBytes, length_setBytes]
        exact hlen208
    -- ── bit clear: square only ──
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      obtain ⟨hrf2, hA4, hws2eq⟩ := hposth
      dsimp only [powFn, powRw] at hrf2 hws2eq heq3a heq3b hws2 ⊢
      rw [exec_selSq_fst] at hrf2
      generalize hpay : leBytes32 (Accel.arith256Mod (wsNat256 ws 176)
        (wsNat256 ws 176) (wsNat256 ws 80) (wsNat256 ws 112)) = pay at hws2eq
      rw [hrf2, hws2eq] at heq3a heq3b
      rw [exec_fetch ebytes _ _ i
        (by rw [length_setBytes]; exact hlen208) hlen
        (by rw [RegFile.get_set_ne _ _ _ _ (by decide),
              RegFile.get_set_ne _ _ _ _ (by decide)]
            exact hx29)
        hif] at heq3a heq3b
      dsimp only at heq3a heq3b
      subst heq3a heq3b
      rw [exec_inc_fst]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hz, hmw, hxw⟩ := id hstag
      have hbit : Crypto.beBit ebytes i = false := by
        dsimp only [Cond.holds] at hnbne
        simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true, RegFile.get_x0, not_not] at hnbne
        cases hgl : Crypto.beBit ebytes i with
        | false => rfl
        | true =>
            exact absurd hnbne (by
              simpa using
                (sll_bit_test (i % 8) (by omega) (ebytes.getD (i / 8) 0)).mpr hgl)
      have hlt_sq : Accel.arith256Mod (wsNat256 ws 176) (wsNat256 ws 176)
          (wsNat256 ws 80) (wsNat256 ws 112) < 2 ^ 256 := by
        show (_ * _ + _) % _ < 2 ^ 256
        rw [hmw]
        exact lt_trans (Nat.mod_lt _ (by omega)) hm256
      dsimp only [ladderInv]
      refine ⟨?_, ?_, by omega, ?_, ?_, ?_⟩
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true, se12_one]
        rw [hx29, ofNat64_succ]
      · simp only [RegFile.get_set_ne, RegFile.get_set_self, ne_eq,
          reduceCtorEq, not_false_eq_true]
        exact hx30
      · exact stagingOk_setBytes hstag
      · rw [← hpay, wsNat256_setBytes_leBytes32 hlt_sq (by omega)]
        rw [show Crypto.ladder m x ebytes (i + 1)
            = Crypto.ladderStep m x (Crypto.ladder m x ebytes i)
              (Crypto.beBit ebytes i) from rfl, hbit, ← hacc]
        show (wsNat256 ws 176 * wsNat256 ws 176 + wsNat256 ws 80)
            % wsNat256 ws 112 = _
        rw [hz, hmw]
        dsimp only [Crypto.ladderStep]
        simp only [Bool.false_eq_true, if_false]
        rw [Nat.add_zero]
      · rw [length_setBytes]
        exact hlen208
  case powmod.post =>
    rintro rf ws A ⟨⟨i, hile, ⟨hx29, hx30, hile', hstag, hacc, hlen208⟩⟩, hncond⟩
    dsimp only [Cond.holds] at hncond
    rw [hx29, hx30] at hncond
    have h1 : (BitVec.ofNat 64 i).toNat = i := toNat_ofNat_lt (by omega)
    have h2 : (BitVec.ofNat 64 (8 * ebytes.length)).toNat
        = 8 * ebytes.length := toNat_ofNat_lt (by omega)
    have hi8 : i = 8 * ebytes.length := by
      simp only [BitVec.ult, decide_eq_true_eq] at hncond
      omega
    subst hi8
    show wsNat256 ws 176 = _
    rw [hacc, Crypto.ladder_correct m x hm ebytes]

end PowLadderDemo
end SAsm
end EvmAsm.Rv64
