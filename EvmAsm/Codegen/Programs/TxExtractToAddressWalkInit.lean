/-
  Extract body: rlp_walk_init call at E+144 (instr 36).

  Scaffold: PCs + Prest + mono available via Spec.walkInit_in_extractLinked.
  Full call packaging (leaf 9-way post + BNE a2=0) residual — use
  `rlp_walk_init_call_within` + HeaderFields pattern next.
-/

import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.RLP.WalkInit
import EvmAsm.Codegen.Programs.TxExtractToAddressSpec
import EvmAsm.Codegen.Programs.TxExtractToAddressLoadType
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen.TxExtractToAddressSpec

open EvmAsm.Rv64
open EvmAsm.Rv64.RLP
open EvmAsm.Codegen

/-- Link after JAL walk_init (instr 37 BNE). -/
abbrev LinkWalkInit : Word := E + 148
/-- After BNE a2=0 not-taken fallthrough. -/
abbrev AfterWalkInitOk : Word := E + 152

private def walkInitJalOff : BitVec 21 :=
  jalOff GuestAddrs.rlp_walk_init (GuestAddrs.tx_extract_to_address + 144)

/-- Leaf pre without ra (call adapter Prest). -/
def extractWalkInitPrest (txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (listOff : Nat) : Assertion :=
  (.x10 ↦ᵣ (txBase + BitVec.ofNat 64 listOff)) ** (.x11 ↦ᵣ listLen) **
    (.x12 ↦ᵣ a2Old) **
    (.x5 ↦ᵣ t0Old) ** (.x6 ↦ᵣ t1Old) ** (.x7 ↦ᵣ t2Old) **
    (.x28 ↦ᵣ t3Old) ** (.x29 ↦ᵣ t4Old) ** (.x30 ↦ᵣ t5Old) ** (.x31 ↦ᵣ t6Old) **
    (.x0 ↦ᵣ (0 : Word)) ** bytesRegion txBase txBytes

local macro "pcf" : tactic =>
  `(tactic| repeat
      first
      | apply pcFree_sepConj
      | exact pcFree_regIs
      | exact pcFree_regOwn
      | exact pcFree_memIs
      | exact pcFree_memOwn
      | exact pcFree_emp
      | exact pcFree_pure
      | exact bytesRegion_pcFree _ _)

theorem extractWalkInitPrest_pcFree
    (txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old : Word)
    (txBytes : List (BitVec 8)) (listOff : Nat) :
    (extractWalkInitPrest txBase listLen a2Old t0Old t1Old t2Old t3Old t4Old t5Old t6Old
      txBytes listOff).pcFree := by
  unfold extractWalkInitPrest; pcf

theorem walkInitJalOff_resolves :
    WalkInitJalPc + signExtend21 walkInitJalOff = WI := by
  simp only [WalkInitJalPc, WI, walkInitJalOff, E]; decide

theorem walkInit_in_extractLinked_available :
    ∀ a i, walkInitCode a = some i → extractLinkedCode a = some i :=
  walkInit_in_extractLinked

#print axioms extractWalkInitPrest_pcFree
#print axioms walkInitJalOff_resolves
#print axioms walkInit_in_extractLinked_available

end EvmAsm.Codegen.TxExtractToAddressSpec
