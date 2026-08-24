/-
  EvmAsm.Codegen.Programs.BalSerializerLeSAsm

  Proof-first (DCode) port of the BAL-serializer BE→LE reversal twins
  `bal_serializer_slot_to_le` / `bal_serializer_balance_to_le`
  (docs/sasm-deriv.md): reverse the 32 BE bytes at `a0` into the fixed
  `.data` scratch buffer the RLP scalar pair reads.

  First user of the PC-aware `blockA` derivation step: the `la` prologue
  (`auipc`+`addi` with the concrete guest-linked `AsmReloc.laHi/laLo`
  immediates) runs on the PC-threaded engine at the routine's own entry
  address, pinned to the actual placement by `callsOk` on the
  caller-shaped path (`DCode.fn_specR`).  The generic derivation takes
  the resolution fact `hla` as a hypothesis; each twin discharges it by
  `decide` on the concrete `GuestAddrs`.

  Byte-identity: `#guard`-pinned against the existing
  `balSerializerSlotToLe_prog` / `balSerializerBalanceToLe_prog`
  (whose emitted strings, with symbolic relocs, already carry their own
  `rfl` drift theorems) — no Codegen change needed.

  The window algebra is the proven generic reverse core
  (`revByte`/`revWin`, len := 32).
-/

import EvmAsm.Rv64.SAsm.Deriv
import EvmAsm.Codegen.Programs.SwrRevLeBeSAsm
import EvmAsm.Codegen.Programs.BalSerializer

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open SwrRevLeBeSAsm (revByte revWin revWin_zero length_revWin revWin_step
  revWin_len_eq execInstrRF_lbu_ro)

namespace BalSerializerLeSAsm

/-! ## The routine's pieces -/

/-- `la` prologue + counters: materialize the destination scratch pointer
    (PC-relative), load the trip count, point at the source MSB. -/
def bslInitBlock (hi : BitVec 20) (lo : BitVec 12) : List Instr :=
  [ .AUIPC .x5 hi,
    .ADDI .x5 .x5 lo,
    .LI .x6 (32 : Word),
    .ADDI .x7 .x10 (31 : BitVec 12) ]

/-- Loop body: copy one source byte (descending) to the destination
    (ascending). -/
def bslStepBlock : List Instr :=
  [ .LBU .x28 .x7 (0 : BitVec 12),
    .SB .x5 .x28 (0 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12) ]

/-- Register file after one loop trip (given the loaded byte). -/
def bslStepRf (rf : RegFile) (b : BitVec 8) : RegFile :=
  let r1 := rf.set .x28 (b.zeroExtend 64)
  let r2 := r1.set .x7 (r1.get .x7 + signExtend12 (-1 : BitVec 12))
  let r3 := r2.set .x5 (r2.get .x5 + signExtend12 (1 : BitVec 12))
  r3.set .x6 (r3.get .x6 + signExtend12 (-1 : BitVec 12))

theorem bslStepRf_get_x5 (rf : RegFile) (b : BitVec 8) :
    (bslStepRf rf b).get .x5 = rf.get .x5 + signExtend12 (1 : BitVec 12) := by
  unfold bslStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28)]

theorem bslStepRf_get_x6 (rf : RegFile) (b : BitVec 8) :
    (bslStepRf rf b).get .x6 = rf.get .x6 + signExtend12 (-1 : BitVec 12) := by
  unfold bslStepRf
  rw [RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x5),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28)]

theorem bslStepRf_get_x7 (rf : RegFile) (b : BitVec 8) :
    (bslStepRf rf b).get .x7 = rf.get .x7 + signExtend12 (-1 : BitVec 12) := by
  unfold bslStepRf
  rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x5),
    RegFile.get_set_self _ _ _ (by decide),
    RegFile.get_set_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]

/-! ## The step engine -/

section Engine

variable (srcBase dstW : Word) (bs : List (BitVec 8))

/-- The source cursor as a natural offset, while in range. -/
theorem bsl_cursor_form (i : Nat) (hi : i < 32) :
    srcBase + (31 : Word) - BitVec.ofNat 64 i
      = srcBase + BitVec.ofNat 64 (31 - i) := by
  have h1 : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 (31 - i)).toNat = 31 - i := by
    rw [BitVec.toNat_ofNat]; omega
  bv_omega

/-- Engine: one trip loads `bs[31-i]` and stores it at window index `i`. -/
theorem bsl_step_engine (i : Nat) (rf : RegFile) (ws : List (BitVec 8))
    (hx5 : rf.get .x5 = dstW + BitVec.ofNat 64 i)
    (hx7 : rf.get .x7 = srcBase + (31 : Word) - BitVec.ofNat 64 i)
    (hi : i < 32)
    (hsrc : srcBase.toNat + 32 < 2 ^ 64) (hdst : dstW.toNat + 32 < 2 ^ 64)
    (hdisj : srcBase.toNat + 32 ≤ dstW.toNat ∨ dstW.toNat + 32 ≤ srcBase.toNat)
    (hws : ws.length = 32) :
    execBlock ⟨srcBase, bs⟩ dstW rf ws bslStepBlock
      = (bslStepRf rf (revByte bs 32 i),
         setBytes ws i [revByte bs 32 i]) := by
  have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by decide
  have h2 : (BitVec.ofNat 64 (31 - i)).toNat = 31 - i := by
    rw [BitVec.toNat_ofNat]; omega
  have hcur : rf.get .x7 + signExtend12 (0 : BitVec 12)
      = srcBase + BitVec.ofNat 64 (31 - i) := by
    rw [hx7, hse_0, bsl_cursor_form srcBase i hi]
    simp
  have hnr : ¬ inRw dstW ws (srcBase + BitVec.ofNat 64 (31 - i)) 1 := by
    unfold inRw
    rw [hws]
    have hsubd : (srcBase + BitVec.ofNat 64 (31 - i) - dstW).toNat
        = (srcBase.toNat + (31 - i) + (2 ^ 64 - dstW.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
      congr 1; omega
    rw [hsubd]
    rcases hdisj with hd | hd <;> omega
  have hsub : (srcBase + BitVec.ofNat 64 (31 - i) - srcBase).toNat
      = 31 - i := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, h2]; omega
  have hstore : ∀ r : RegFile, r.get .x5 = dstW + BitVec.ofNat 64 i →
      (r.get .x5 + signExtend12 (0 : BitVec 12) - dstW).toNat = i := by
    intro r h
    rw [h, hse_0]
    have hi2 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]; omega
    bv_omega
  rw [show bslStepBlock =
      [.LBU .x28 .x7 (0 : BitVec 12), .SB .x5 .x28 (0 : BitVec 12),
       .ADDI .x7 .x7 (-1 : BitVec 12), .ADDI .x5 .x5 (1 : BitVec 12),
       .ADDI .x6 .x6 (-1 : BitVec 12)] from rfl]
  rw [execBlock_cons,
    execInstrRF_lbu_ro _ _ _ _ _ _ _ (by rw [hcur]; exact hnr)]
  dsimp only
  rw [show Region.byteAt ⟨srcBase, bs⟩ _ = revByte bs 32 i from by
    rw [hcur]
    show bs.getD ((srcBase + BitVec.ofNat 64 (31 - i) - srcBase).toNat) 0
      = revByte bs 32 i
    rw [hsub]; rfl]
  rw [execBlock_cons, execInstrRF_sb_byte _ _ _ _ _ _ _ i
    (by
      refine hstore _ ?_
      rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x28), hx5])]
  dsimp only
  have hb : ∀ (r : RegFile) (v : BitVec 8),
      BitVec.truncate 8 ((r.set .x28 (v.zeroExtend 64)).get .x28) = v := by
    intro r v
    rw [RegFile.get_set_self _ _ _ (by decide), truncate_zeroExtend_byte]
  rw [hb]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_cons]
  dsimp only [execInstrRF, aluSem]
  rw [execBlock_nil]
  unfold bslStepRf
  rw [setBytes_singleton]

end Engine

/-! ## The generic derivation -/

section Deriv

variable (entry dstW srcBase : Word) (hi : BitVec 20) (lo : BitVec 12)
  (bs orig : List (BitVec 8))

/-- Static facts. -/
def bslStatic : Prop :=
  orig.length = 32 ∧ 32 ≤ bs.length ∧
  srcBase.toNat + 32 < 2 ^ 64 ∧ dstW.toNat + 32 < 2 ^ 64 ∧
  (srcBase.toNat + 32 ≤ dstW.toNat ∨ dstW.toNat + 32 ≤ srcBase.toNat)

/-- Loop invariant. -/
def bslInv (i : Nat) : Reach :=
  fun rf ws A =>
    rf.get .x5 = dstW + BitVec.ofNat 64 i ∧
    rf.get .x6 = BitVec.ofNat 64 (32 - i) ∧
    rf.get .x7 = srcBase + (31 : Word) - BitVec.ofNat 64 i ∧
    i ≤ 32 ∧ bslStatic dstW srcBase bs orig ∧
    ws = revWin bs 32 orig i ∧ A = empAssertion

local infix:36 " ⤳ " => DCode (Region.mk srcBase bs) (RwRegion.mk dstW 32)

/-- Proof-first BE→LE reversal into a fixed `.data` scratch buffer: `la`
    the destination (PC-aware `blockA` at the routine's entry), then a
    32-trip descending-source/ascending-destination byte copy. -/
def bslDeriv
    (hla : entry + (((hi.zeroExtend 32 : BitVec 32)) <<< 12).signExtend 64
        + signExtend12 lo = dstW) :
    (fun rf ws A => rf.get .x10 = srcBase ∧ ws = orig ∧
      bslStatic dstW srcBase bs orig ∧ A = empAssertion)
      ⤳ (fun _ ws A => ws = (bs.take 32).reverse ∧ A = empAssertion) :=
  calc (fun rf ws A => rf.get .x10 = srcBase ∧ ws = orig ∧
        bslStatic dstW srcBase bs orig ∧ A = empAssertion : Reach)
    _ ⤳ (fun rf ws A => bslInv dstW srcBase bs orig 0 rf ws A : Reach) :=
      DCode.blockA "la" entry (bslInitBlock hi lo) rfl
        (fun h => nomatch h)
        (by
          rintro rf ws A _ ⟨h10, hws, hst, hA⟩
          simp only [bslInitBlock, execBlockAt, execInstrRFAt, execInstrRF,
            aluSem, bslInv]
          refine ⟨?_, ?_, ?_, by omega, hst, by rw [hws, revWin_zero], hA⟩
          · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x7),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x5 ≠ .x6),
              RegFile.get_set_self _ _ _ (by decide),
              RegFile.get_set_self _ _ _ (by decide), hla]
            simp
          · rw [RegFile.get_set_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7),
              RegFile.get_set_self _ _ _ (by decide)]
            rfl
          · rw [RegFile.get_set_self _ _ _ (by decide),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x6),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
              RegFile.get_set_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5), h10]
            rw [show signExtend12 (31 : BitVec 12) = (31 : Word) from
              by decide]
            bv_omega)
    _ ⤳ (fun rf ws A => (∃ i, i ≤ 32 ∧ bslInv dstW srcBase bs orig i rf ws A)
          ∧ ¬ (Cond.bne .x6 .x0).holds rf : Reach) :=
      DCode.dwhile "loop" (.bne .x6 .x0) 32 (bslInv dstW srcBase bs orig)
        (fun _ _ _ h => h)
        (fun i =>
          DCode.block "step" bslStepBlock (by decide)
            (by
              intro _ rf ws A hwslen hpre
              obtain ⟨hik, ⟨h5, h6, h7, hile,
                ⟨hol, hlb, hsb, hdb, hdj⟩, hwin, hA⟩, -⟩ := hpre
              have hws32 : ws.length = 32 := hwslen
              have hse_0 : signExtend12 (0 : BitVec 12) = (0 : Word) := by
                decide
              have h2 : (BitVec.ofNat 64 (31 - i)).toNat = 31 - i := by
                rw [BitVec.toNat_ofNat]; omega
              have hcur : rf.get .x7 + signExtend12 (0 : BitVec 12)
                  = srcBase + BitVec.ofNat 64 (31 - i) := by
                rw [h7, hse_0, bsl_cursor_form srcBase i hik]
                simp
              have hnr : ¬ inRw dstW ws
                  (srcBase + BitVec.ofNat 64 (31 - i)) 1 := by
                unfold inRw
                rw [hws32]
                have hsubd : (srcBase + BitVec.ofNat 64 (31 - i)
                    - dstW).toNat
                    = (srcBase.toNat + (31 - i) + (2 ^ 64 - dstW.toNat))
                      % 2 ^ 64 := by
                  rw [BitVec.toNat_sub, BitVec.toNat_add, h2]
                  congr 1; omega
                rw [hsubd]
                rcases hdj with hd | hd <;> omega
              show blockVCs ⟨srcBase, bs⟩ dstW rf ws bslStepBlock
              rw [show bslStepBlock =
                  [.LBU .x28 .x7 (0 : BitVec 12), .SB .x5 .x28 (0 : BitVec 12),
                   .ADDI .x7 .x7 (-1 : BitVec 12),
                   .ADDI .x5 .x5 (1 : BitVec 12),
                   .ADDI .x6 .x6 (-1 : BitVec 12)] from rfl]
              refine ⟨?_, ?_⟩
              · -- LBU: read-only region, in range
                simp only [loadSem]
                rw [if_neg (by rw [hcur]; exact hnr)]
                rw [hcur]
                show 1 ∣ (srcBase + BitVec.ofNat 64 (31 - i)
                    - srcBase).toNat
                  ∧ (srcBase + BitVec.ofNat 64 (31 - i) - srcBase).toNat + 1
                    ≤ bs.length
                have hsub : (srcBase + BitVec.ofNat 64 (31 - i)
                    - srcBase).toNat = 31 - i := by
                  rw [BitVec.toNat_sub, BitVec.toNat_add, h2]; omega
                rw [hsub]
                exact ⟨Nat.one_dvd _, by omega⟩
              · rw [execInstrRF_lbu_ro _ _ _ _ _ _ _
                  (by rw [hcur]; exact hnr)]
                have hidx : ∀ v : Word, ((rf.set .x28 v).get .x5
                    + signExtend12 (0 : BitVec 12) - dstW).toNat = i := by
                  intro v
                  rw [RegFile.get_set_ne _ _ _ _
                      (by decide : Reg.x5 ≠ .x28), h5, hse_0]
                  have hi2 : (BitVec.ofNat 64 i).toNat = i := by
                    rw [BitVec.toNat_ofNat]; omega
                  bv_omega
                refine ⟨⟨?_, ?_⟩, trivial, trivial, trivial, trivial⟩
                · dsimp only
                  unfold inRw
                  rw [hidx _, hws32]
                  omega
                · dsimp only
                  rw [hidx _]
                  exact Nat.one_dvd _)
            (by
              rintro rf ws A hwslen ⟨hik, ⟨h5, h6, h7, hile, hst,
                hwin, hA⟩, -⟩
              obtain ⟨hol, hlb, hsb, hdb, hdj⟩ := hst
              have hws32 : ws.length = 32 := hwslen
              rw [bsl_step_engine srcBase dstW bs i rf ws h5 h7 hik
                hsb hdb hdj hws32]
              refine ⟨?_, ?_, ?_, by omega,
                ⟨hol, hlb, hsb, hdb, hdj⟩, ?_, hA⟩
              · rw [bslStepRf_get_x5, h5,
                  show signExtend12 (1 : BitVec 12) = (1 : Word) from
                    by decide]
                have h1 : (BitVec.ofNat 64 i).toNat = i := by
                  rw [BitVec.toNat_ofNat]; omega
                have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
                  rw [BitVec.toNat_ofNat]; omega
                bv_omega
              · rw [bslStepRf_get_x6, h6,
                  show signExtend12 (-1 : BitVec 12) = (-1 : Word) from
                    by decide]
                have h1 : (BitVec.ofNat 64 (32 - i)).toNat = 32 - i := by
                  rw [BitVec.toNat_ofNat]; omega
                have h2 : (BitVec.ofNat 64 (32 - (i + 1))).toNat
                    = 32 - (i + 1) := by rw [BitVec.toNat_ofNat]; omega
                bv_omega
              · rw [bslStepRf_get_x7, h7,
                  show signExtend12 (-1 : BitVec 12) = (-1 : Word) from
                    by decide]
                have h1 : (BitVec.ofNat 64 i).toNat = i := by
                  rw [BitVec.toNat_ofNat]; omega
                have h2 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
                  rw [BitVec.toNat_ofNat]; omega
                bv_omega
              · rw [hwin, revWin_step bs 32 orig i hol hik]))
        (fun rf ws A h => by
          obtain ⟨-, h6, -⟩ := h
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not]
          rw [h6]
          decide)
    _ ⤳ (fun _ ws A => ws = (bs.take 32).reverse ∧ A = empAssertion : Reach) :=
      DCode.pure "done"
        (by
          rintro rf ws A ⟨⟨i, hile, -, h6, -, -, ⟨hol, hlb, -, -, -⟩,
            hwin, hA⟩, hc⟩
          simp only [Cond.holds, RegFile.get_x0, ne_eq, not_not] at hc
          have hi32 : i = 32 := by
            rw [h6] at hc
            have := congrArg BitVec.toNat hc
            rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl]
              at this
            omega
          subst hi32
          exact ⟨by rw [hwin, revWin_len_eq bs 32 orig hol hlb], hA⟩)

/-- The generic function. -/
def bslFn (name : String)
    (hla : entry + (((hi.zeroExtend 32 : BitVec 32)) <<< 12).signExtend 64
        + signExtend12 lo = dstW) : Fn :=
  (bslDeriv entry dstW srcBase hi lo bs orig hla).fn name

/-- Machine-level correctness at the routine's own entry (the `la` is
    PC-relative, so the placement is pinned): from the ABI precondition,
    the 32-byte scratch window ends as the reversed source bytes. -/
theorem bslFn_spec (name : String)
    (hla : entry + (((hi.zeroExtend 32 : BitVec 32)) <<< 12).signExtend 64
        + signExtend12 lo = dstW)
    (hreg : (Region.mk srcBase bs).wf) (hrw : RwRegion.wf ⟨dstW, 32⟩) :
    (bslFn entry dstW srcBase hi lo bs orig name hla).SpecR entry
      (CodeReq.ofProg entry
        ((bslFn entry dstW srcBase hi lo bs orig name hla).body.flatten
          entry)) :=
  DCode.fn_specR name (bslDeriv entry dstW srcBase hi lo bs orig hla)
    entry _ hreg hrw (fun _ _ h => h)
    (show (True ∧ True) ∧ True from ⟨⟨trivial, trivial⟩, trivial⟩)
    (show ((entry = entry) ∧ True) ∧ True from ⟨⟨rfl, trivial⟩, trivial⟩)

end Deriv

/-! ## The two twins -/

/-- `Program` is a def alias, opaque to instance search. -/
instance : BEq Program := inferInstanceAs (BEq (List Instr))

/-- `bal_serializer_slot_to_le` as a generated `Fn`. -/
def slotToLeFn (srcBase : Word) (bs orig : List (BitVec 8)) : Fn :=
  bslFn (BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_to_le)
    (BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_le) srcBase
    (laHi GuestAddrs.bal_serializer_slot_le
      (GuestAddrs.bal_serializer_slot_to_le + 0))
    (laLo GuestAddrs.bal_serializer_slot_le
      (GuestAddrs.bal_serializer_slot_to_le + 0))
    bs orig "bal_serializer_slot_to_le" (by decide)

/-- `bal_serializer_slot_to_le`, at its guest placement: the 32-byte
    `bal_serializer_slot_le` scratch ends as the reversed source bytes. -/
theorem slotToLeFn_spec (srcBase : Word) (bs orig : List (BitVec 8))
    (hreg : (Region.mk srcBase bs).wf)
    (hrw : RwRegion.wf
      ⟨BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_le, 32⟩) :
    (slotToLeFn srcBase bs orig).SpecR
      (BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_to_le)
      (CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_to_le)
        ((slotToLeFn srcBase bs orig).body.flatten
          (BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_to_le))) :=
  bslFn_spec _ _ srcBase _ _ bs orig _ _ hreg hrw

-- Byte-identity with the emitted program (whose string carries its own
-- rfl drift theorem in BalSerializer.lean).
#guard (((slotToLeFn 0 [] []).programRet
      (BitVec.ofNat 64 GuestAddrs.bal_serializer_slot_to_le)) : List Instr)
    == (balSerializerSlotToLe_prog : List Instr)

/-- `bal_serializer_balance_to_le` as a generated `Fn`. -/
def balanceToLeFn (srcBase : Word) (bs orig : List (BitVec 8)) : Fn :=
  bslFn (BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_to_le)
    (BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_le) srcBase
    (laHi GuestAddrs.bal_serializer_balance_le
      (GuestAddrs.bal_serializer_balance_to_le + 0))
    (laLo GuestAddrs.bal_serializer_balance_le
      (GuestAddrs.bal_serializer_balance_to_le + 0))
    bs orig "bal_serializer_balance_to_le" (by decide)

/-- `bal_serializer_balance_to_le`, at its guest placement. -/
theorem balanceToLeFn_spec (srcBase : Word) (bs orig : List (BitVec 8))
    (hreg : (Region.mk srcBase bs).wf)
    (hrw : RwRegion.wf
      ⟨BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_le, 32⟩) :
    (balanceToLeFn srcBase bs orig).SpecR
      (BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_to_le)
      (CodeReq.ofProg
        (BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_to_le)
        ((balanceToLeFn srcBase bs orig).body.flatten
          (BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_to_le))) :=
  bslFn_spec _ _ srcBase _ _ bs orig _ _ hreg hrw

#guard (((balanceToLeFn 0 [] []).programRet
      (BitVec.ofNat 64 GuestAddrs.bal_serializer_balance_to_le)) : List Instr)
    == (balSerializerBalanceToLe_prog : List Instr)

end BalSerializerLeSAsm

end EvmAsm.Codegen
