/-
  EvmAsm.Codegen.Programs.MptEarlyRetShape

  **Byte-identity check for the early-return-from-loop shape** (bead
  evm-asm-4ch8f.70.2, resolving shape-survey §4.2 by OPTION 1 —
  whileBreak-to-epilogue, byte-transparent).

  The survey flagged `mpt_set` / `mpt_insert` as the only routines whose
  bubble-up loop "returns from the function" mid-scan.  This file pins,
  kernel-checked and against the ACTUAL emitted bytes of the linked-image
  variants (`mptSetAcc_prog` / `mptInsertAcc_prog`, the verification targets
  of beads .29/.31), that the shape is exactly the one
  `EvmAsm/Rv64/SAsm/RetFromLoop.lean` resolves:

  * each routine has exactly ONE `ret` (`jalr x0, x1, 0`) — there is no
    second frame restore, so "both paths restore the same frame" holds by
    construction (the survey's option-1 side condition);
  * the loop break and every parse-fail branch target a 2-instruction fail
    stub `li a0, 2 ; j <epilogue>` whose bytes are LITERALLY
    `liJumpTailProg [(.x10, 2)] (-56)` — the jump-join tail combinator's
    emitted shape;
  * the stub's `JAL x0` lands on the shared frame-restore epilogue entry
    (`ld ra, 0(sp)`), the same instruction the fall-through post reaches.

  All layout facts are RELATIVE (instruction indices / branch immediates);
  the two `*_failTail_spec` theorems are stated at a SYMBOLIC base — no
  `GuestAddrs` value pins (post-af3rp #10103).  They are the reusable
  break-arm lemmas the .31 ports instantiate: given the routine's shared
  epilogue continuation, the mid-loop "return" is a `jumpJoinTail_spec`
  instance on the real bytes.

  Layout (relative to each routine's entry, in instruction slots):

    mpt_set_acc (121 instrs)          mpt_insert_acc (689 instrs)
      +57  loop hdr  beqz s7 → +100     +622 loop hdr  beqz s7 → +666
      +83  break     bnez a0 → +119     +648 break     bnez a0 → +687
      +99  back-edge j → +57            +665 back-edge j → +622
      +100 post (keccak, li a0, 0)      +666 post (keccak, li a0, 0)
      +106 epilogue  ld ra, 0(sp) …     +674 epilogue  ld ra, 0(sp) …
      +118 THE ret                      +686 THE ret
      +119 fail: li a0, 2 ; j +106      +687 fail: li a0, 2 ; j +674
-/

import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Rv64.SAsm.RetFromLoop

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace MptEarlyRetShape

/-! ## The emitted programs at `List Instr`
    (the `Program` alias is a plain `def`, opaque to `GetElem`). -/

private def msaProg : List Instr := mptSetAcc_prog
private def miaProg : List Instr := mptInsertAcc_prog

/-! ## Geometry pins — `mpt_set_acc` -/

-- Exactly ONE `ret` in the whole routine: the shared epilogue's.
#guard (msaProg.filter
  (fun i => i = Instr.JALR .x0 .x1 (0 : BitVec 12))).length = 1
-- Loop header guard exits to the post (+100), past the back-edge.
#guard msaProg[57]? = some (.BEQ .x23 .x0 (172 : BitVec 13))
#guard 4 * 57 + 172 = 4 * 100
-- The mid-loop break targets the fail stub (+119), past the `ret`.
#guard msaProg[83]? = some (.BNE .x10 .x0 (144 : BitVec 13))
#guard 4 * 83 + 144 = 4 * 119
-- Back-edge returns to the header.
#guard msaProg[99]? = some (.JAL .x0 (-168 : BitVec 21))
#guard 4 * 99 - 168 = 4 * 57
-- The single shared epilogue: frame-restore entry (+106) … `ret` (+118).
#guard msaProg[106]? = some (.LD .x1 .x2 (0 : BitVec 12))
#guard msaProg[118]? = some (.JALR .x0 .x1 (0 : BitVec 12))
-- **The fail stub IS the jump-join tail combinator's byte shape**, and its
-- backward jump lands on the shared epilogue entry.
#guard msaProg.drop 119 = liJumpTailProg [(.x10, (2 : Word))] (-56 : BitVec 21)
#guard 4 * 120 - 56 = 4 * 106
-- The pre-loop early exits also route through the SAME epilogue / stub:
-- walk-status propagation straight to the epilogue, leaf-encode failure to
-- the fail stub.
#guard msaProg[26]? = some (.BNE .x10 .x0 (320 : BitVec 13))
#guard 4 * 26 + 320 = 4 * 106
#guard msaProg[40]? = some (.BNE .x10 .x0 (316 : BitVec 13))
#guard 4 * 40 + 316 = 4 * 119

/-! ## Geometry pins — `mpt_insert_acc` -/

#guard (miaProg.filter
  (fun i => i = Instr.JALR .x0 .x1 (0 : BitVec 12))).length = 1
#guard miaProg[622]? = some (.BEQ .x23 .x0 (176 : BitVec 13))
#guard 4 * 622 + 176 = 4 * 666
#guard miaProg[648]? = some (.BNE .x10 .x0 (156 : BitVec 13))
#guard 4 * 648 + 156 = 4 * 687
#guard miaProg[665]? = some (.JAL .x0 (-172 : BitVec 21))
#guard 4 * 665 - 172 = 4 * 622
#guard miaProg[674]? = some (.LD .x1 .x2 (0 : BitVec 12))
#guard miaProg[686]? = some (.JALR .x0 .x1 (0 : BitVec 12))
#guard miaProg.drop 687 = liJumpTailProg [(.x10, (2 : Word))] (-56 : BitVec 21)
#guard 4 * 688 - 56 = 4 * 674
-- Insert-walk status propagation goes straight to the shared epilogue.
#guard miaProg[32]? = some (.BNE .x10 .x0 (2568 : BitVec 13))
#guard 4 * 32 + 2568 = 4 * 674

/-! ## The fail-stub triples on the REAL bytes (symbolic base)

    Each is the `jumpJoinTail_spec` instance on the emitted program: from
    ownership of `a0`, the stub pins `a0 = 2` and reaches the routine's
    `ret` continuation THROUGH the given shared-epilogue triple — the
    break arm the .31 loop proofs (`breakStation_spec` /
    `twoBreakRetLoop_spec`) will consume. -/

/-- `mpt_set_acc`'s mid-loop "function return": the fail stub at `+476`
    joins the shared epilogue at `+424`. -/
theorem mptSetAcc_failTail_spec {m : Nat} (base ret : Word) {F Q : Assertion}
    (hF : F.pcFree)
    (hepi : cpsTripleWithin m (base + 424) ret
      (CodeReq.ofProg base mptSetAcc_prog)
      (((.x10 : Reg) ↦ᵣ (2 : Word)) ** F) Q) :
    cpsTripleWithin (2 + m) (base + 476) ret
      (CodeReq.ofProg base mptSetAcc_prog)
      (regOwn .x10 ** F) Q := by
  have h := jumpJoinTail_spec (m := m)
    (CodeReq.ofProg base mptSetAcc_prog) (base + 476) ret
    (-56 : BitVec 21) [(.x10, (2 : Word))] (F := F)
    (by decide) (by decide)
    (CodeReq.ofProg_mono_sub base (base + 476) mptSetAcc_prog
      (liJumpTailProg [(.x10, (2 : Word))] (-56 : BitVec 21)) 119 rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    hF
    (by
      rw [show (base + 476)
          + BitVec.ofNat 64
            (4 * ([((.x10 : Reg), (2 : Word))] : List (Reg × Word)).length)
          + signExtend21 (-56 : BitVec 21) = base + 424 from by
        rw [BitVec.add_assoc, BitVec.add_assoc]
        congr 1]
      exact cpsTripleWithin_weaken
        (fun h hp => by
          simp only [regsSet_cons, regsSet_nil, sepConj_emp_right'] at hp
          exact hp)
        (fun _ hq => hq) hepi)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) h
  simp only [List.map_cons, List.map_nil, regOwns_cons, regOwns_nil,
    sepConj_emp_right']
  exact hp


/-- `mpt_insert_acc`'s mid-loop "function return": the fail stub at `+2748`
    joins the shared epilogue at `+2696`. -/
theorem mptInsertAcc_failTail_spec {m : Nat} (base ret : Word) {F Q : Assertion}
    (hF : F.pcFree)
    (hepi : cpsTripleWithin m (base + 2696) ret
      (CodeReq.ofProg base mptInsertAcc_prog)
      (((.x10 : Reg) ↦ᵣ (2 : Word)) ** F) Q) :
    cpsTripleWithin (2 + m) (base + 2748) ret
      (CodeReq.ofProg base mptInsertAcc_prog)
      (regOwn .x10 ** F) Q := by
  have h := jumpJoinTail_spec (m := m)
    (CodeReq.ofProg base mptInsertAcc_prog) (base + 2748) ret
    (-56 : BitVec 21) [(.x10, (2 : Word))] (F := F)
    (by decide) (by decide)
    (CodeReq.ofProg_mono_sub base (base + 2748) mptInsertAcc_prog
      (liJumpTailProg [(.x10, (2 : Word))] (-56 : BitVec 21)) 687 rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    hF
    (by
      rw [show (base + 2748)
          + BitVec.ofNat 64
            (4 * ([((.x10 : Reg), (2 : Word))] : List (Reg × Word)).length)
          + signExtend21 (-56 : BitVec 21) = base + 2696 from by
        rw [BitVec.add_assoc, BitVec.add_assoc]
        congr 1]
      exact cpsTripleWithin_weaken
        (fun h hp => by
          simp only [regsSet_cons, regsSet_nil, sepConj_emp_right'] at hp
          exact hp)
        (fun _ hq => hq) hepi)
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq) h
  simp only [List.map_cons, List.map_nil, regOwns_cons, regOwns_nil,
    sepConj_emp_right']
  exact hp


end MptEarlyRetShape

end EvmAsm.Codegen
