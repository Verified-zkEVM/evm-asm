/-
  Spec substrate for `tx_eip7702_existing_authority_refund` (teer, 745-instr).

  Targets `TeerAssumed.applied_flat` (BlockVerdictTxStateGasArraySpec):
    a0 = teer APPLIED state charge; bal≠0 path; ambient tx + BAL regions;
    s0–s11 restored; teerScratchOwn preserved ownership.

  Callees (type_dispatch, walks, recover, bal_*, …) enter as named hyps
  under `TeerCalleeAssumptions` — discharged leaf-by-leaf (prover1).
-/

import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArraySpec
import EvmAsm.Codegen.Programs.BlockVerdictTxStateGasArrayModel
import EvmAsm.Codegen.Programs.TxTypeDispatchSpec
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SAsm.AbiFrame
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Rv64.RLP.WalkNext
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxEip7702TeerSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen
open EvmAsm.Codegen.BlockVerdictTxStateGasArrayModel
open EvmAsm.Codegen.BlockVerdictTxStateGasArraySpec
  (nTeerSteps nTeerStackDwords teerScratchOwn pcFree_teerScratchOwn)

abbrev E : Word := BitVec.ofNat 64 GuestAddrs.tx_eip7702_existing_authority_refund
abbrev teerProg : Program := txEip7702ExistingAuthorityRefund_prog
abbrev teerCode : CodeReq := CodeReq.ofProg E teerProg

set_option maxRecDepth 8000 in
theorem teer_length : teerProg.length = 745 := rfl

theorem teer_bound : 4 * teerProg.length < 2 ^ 64 := by
  simp only [teer_length]; decide

/-- type_dispatch leaf (shared with extract/intrinsic). -/
abbrev typeProg : Program := txTypeDispatch_prog
abbrev typeCode : CodeReq :=
  CodeReq.ofProg (BitVec.ofNat 64 GuestAddrs.tx_type_dispatch) typeProg

theorem type_length' : typeProg.length = 45 := by decide

abbrev walkInitCode : CodeReq :=
  rlp_walk_init_code (BitVec.ofNat 64 GuestAddrs.rlp_walk_init)
abbrev walkNextCode : CodeReq :=
  rlp_walk_next_code (BitVec.ofNat 64 GuestAddrs.rlp_walk_next)

/-- Minimal linked code for early teer segments (type + walks).
    Auth-loop callees join later under TeerCalleeAssumptions. -/
def teerLinkedEarly : CodeReq :=
  ((teerCode.union typeCode).union walkInitCode).union walkNextCode

/-- 14-slot frame: ra, s0–s11 (x8,x9,x18–x27), a5 (x15) at +104.
    Leaf does `addi sp,-160` (20 dwords); slots use 112B, rest local scratch. -/
def teerFrame : FrameDesc :=
  [(.x1, 0), (.x8, 8), (.x9, 16),
   (.x18, 24), (.x19, 32), (.x20, 40), (.x21, 48), (.x22, 56),
   (.x23, 64), (.x24, 72), (.x25, 80), (.x26, 88), (.x27, 96),
   (.x15, 104)]

theorem teerFrame_length : teerFrame.length = 14 := by decide

structure TeerSaved where
  ra : Word
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
  s5 : Word
  s6 : Word
  s7 : Word
  s8 : Word
  s9 : Word
  s10 : Word
  s11 : Word
  a5 : Word

def teerSavedVals (s : TeerSaved) : Reg → Word
  | .x1  => s.ra
  | .x8  => s.s0
  | .x9  => s.s1
  | .x18 => s.s2
  | .x19 => s.s3
  | .x20 => s.s4
  | .x21 => s.s5
  | .x22 => s.s6
  | .x23 => s.s7
  | .x24 => s.s8
  | .x25 => s.s9
  | .x26 => s.s10
  | .x27 => s.s11
  | .x15 => s.a5
  | _ => 0

/-- PC after frame save (ADDI + 14 SD = 15 instr → E+60). -/
abbrev AfterFrameSave : Word := E + 60
/-- PC after ABI moves s0..s4 (5 MV → E+80). -/
abbrev AfterAbiMoves : Word := E + 80
/-- PC after `li s10, 0` (E+84); start of scratch-zero la sequence. -/
abbrev AfterLiS10 : Word := E + 84
/-- PC at bal≠0 BEQ (after 4× la/sd zero triples = 12 instr → E+132). -/
abbrev AtBalCheck : Word := E + 132

/-- Stack delta: `addi sp, -160`. -/
def teerSpDelta : BitVec 12 := -160

end EvmAsm.Codegen.TxEip7702TeerSpec
