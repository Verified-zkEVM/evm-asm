/-
  Constructive K67 status-0 witness. This is kept in-tree so the
  non-vacuity probe is kernel-checked rather than living in /tmp.
-/
import EvmAsm.Codegen.Programs.HeaderValidatePostMergeBridge
namespace EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge
open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Stateless.SpecRef
def k67HeaderBytesLiteral : Bytes := [0xf9, 0x02, 0x75, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a, 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a, 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13, 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb9, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x80, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80]
set_option maxRecDepth 8000 in
/-- A canonical 23-field Amsterdam header satisfies the machine's status-0
    guard, so the bridge's decode-success arm has a concrete inhabitant. -/
theorem k67GuardOk_constructive_witness :
    EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec.k67GuardOk (0 : Word)
    k67HeaderBytesLiteral := by
  unfold EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec.k67GuardOk
  have h0 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 3
      (BitVec.ofNat 64 3) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 36) (BitVec.ofNat 64 32) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xa0, by decide, ?_⟩
    exact Or.inr (by decide)
  have h1 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 36
      (BitVec.ofNat 64 36) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 69) (BitVec.ofNat 64 32) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xa0, by decide, ?_⟩
    exact Or.inr (by decide)
  have h2 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 69
      (BitVec.ofNat 64 69) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 90) (BitVec.ofNat 64 20) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x94, by decide, ?_⟩
    exact Or.inr (by decide)
  have h3 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 90
      (BitVec.ofNat 64 90) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 123) (BitVec.ofNat 64 32) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xa0, by decide, ?_⟩
    exact Or.inr (by decide)
  have h4 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 123
      (BitVec.ofNat 64 123) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 156) (BitVec.ofNat 64 32) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xa0, by decide, ?_⟩
    exact Or.inr (by decide)
  have h5 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 156
      (BitVec.ofNat 64 156) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 189) (BitVec.ofNat 64 32) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xa0, by decide, ?_⟩
    exact Or.inr (by decide)
  have h6 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 189
      (BitVec.ofNat 64 189) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 448) (BitVec.ofNat 64 256) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xb9, by decide, ?_⟩
    exact Or.inr (Or.inr (Or.inl (by decide)))
  have h7 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 448
      (BitVec.ofNat 64 448) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 449) (BitVec.ofNat 64 0) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x80, by decide, ?_⟩
    exact Or.inr (by decide)
  have h8 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 449
      (BitVec.ofNat 64 449) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 450) (BitVec.ofNat 64 0) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x80, by decide, ?_⟩
    exact Or.inr (by decide)
  have h9 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 450
      (BitVec.ofNat 64 450) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 451) (BitVec.ofNat 64 0) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x80, by decide, ?_⟩
    exact Or.inr (by decide)
  have h10 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 451
      (BitVec.ofNat 64 451) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 452) (BitVec.ofNat 64 0) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x80, by decide, ?_⟩
    exact Or.inr (by decide)
  have h11 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 452
      (BitVec.ofNat 64 452) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 453) (BitVec.ofNat 64 0) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x80, by decide, ?_⟩
    exact Or.inr (by decide)
  have h12 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 453
      (BitVec.ofNat 64 453) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 454) (BitVec.ofNat 64 0) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x80, by decide, ?_⟩
    exact Or.inr (by decide)
  have h13 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 454
      (BitVec.ofNat 64 454) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 487) (BitVec.ofNat 64 32) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0xa0, by decide, ?_⟩
    exact Or.inr (by decide)
  have h14 : EvmAsm.Rv64.RLP.rlpItemDecode k67HeaderBytesLiteral 487
      (BitVec.ofNat 64 487) (BitVec.ofNat 64 632)
      (BitVec.ofNat 64 496) (BitVec.ofNat 64 8) := by
    unfold EvmAsm.Rv64.RLP.rlpItemDecode
    refine ⟨0x88, by decide, ?_⟩
    exact Or.inr (by decide)
  have hp0 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 0 3 := .zero
  have hp1 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 1 36 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 0 3 (BitVec.ofNat 64 36) (BitVec.ofNat 64 32) hp0 h0)
  have hp2 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 2 69 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 1 36 (BitVec.ofNat 64 69) (BitVec.ofNat 64 32) hp1 h1)
  have hp3 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 3 90 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 2 69 (BitVec.ofNat 64 90) (BitVec.ofNat 64 20) hp2 h2)
  have hp4 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 4 123 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 3 90 (BitVec.ofNat 64 123) (BitVec.ofNat 64 32) hp3 h3)
  have hp5 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 5 156 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 4 123 (BitVec.ofNat 64 156) (BitVec.ofNat 64 32) hp4 h4)
  have hp6 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 6 189 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 5 156 (BitVec.ofNat 64 189) (BitVec.ofNat 64 32) hp5 h5)
  have hp7 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 7 448 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 6 189 (BitVec.ofNat 64 448) (BitVec.ofNat 64 256) hp6 h6)
  have hp8 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 8 449 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 7 448 (BitVec.ofNat 64 449) (BitVec.ofNat 64 0) hp7 h7)
  have hp9 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 9 450 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 8 449 (BitVec.ofNat 64 450) (BitVec.ofNat 64 0) hp8 h8)
  have hp10 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 10 451 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 9 450 (BitVec.ofNat 64 451) (BitVec.ofNat 64 0) hp9 h9)
  have hp11 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 11 452 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 10 451 (BitVec.ofNat 64 452) (BitVec.ofNat 64 0) hp10 h10)
  have hp12 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 12 453 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 11 452 (BitVec.ofNat 64 453) (BitVec.ofNat 64 0) hp11 h11)
  have hp13 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 13 454 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 12 453 (BitVec.ofNat 64 454) (BitVec.ofNat 64 0) hp12 h12)
  have hp14 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 14 487 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 13 454 (BitVec.ofNat 64 487) (BitVec.ofNat 64 32) hp13 h13)
  have hp15 : EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix k67HeaderBytesLiteral (0 : Word) (BitVec.ofNat 64 632) 3 15 496 := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.succ 14 487 (BitVec.ofNat 64 496) (BitVec.ofNat 64 8) hp14 h14)
  have hn1 := EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.select hp1 h1
  have hn7 := EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.select hp7 h7
  have hn14 := EvmAsm.Codegen.RlpListNthItemSAsm.StrictPrefix.select hp14 h14
  have houter : EvmAsm.Codegen.RlpListNthItemSAsm.StrictListPayload k67HeaderBytesLiteral (0 : Word)
      k67HeaderBytesLiteral.length 3 (0 + BitVec.ofNat 64 k67HeaderBytesLiteral.length) := by
    simpa using (EvmAsm.Codegen.RlpListNthItemSAsm.strictListPayload_long_forward
      k67HeaderBytesLiteral (0 : Word) 0xf9 2 629 (by decide) (by decide)
      (by decide) (by decide) (by decide))
  refine ⟨3, 487, 496, 8, 69, 32, 449, ?_, rfl, ?_, rfl, ?_⟩
  · exact ⟨⟨hp15, hn1, hn7, hn14, h14⟩, houter⟩
  · intro k hk
    interval_cases k <;> decide
  · intro k hk
    interval_cases k <;> decide

set_option maxRecDepth 8000 in
/-- The canonical status-0 witness cannot also satisfy the guest-only
    status-12 guard.  The outer-list cursor identifies the existential start,
    and the proven field-14 chain supplies a decode after every prefix of at
    most fourteen items. -/
theorem k67GuardFail_excludes_canonical_literal :
    ¬ EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec.k67GuardFail (0 : Word)
      k67HeaderBytesLiteral (by decide) := by
  intro hfail
  rcases hfail with hwalk | hinit
  · rcases hwalk with ⟨startOff, i, cur, statusW, hne, hile, hcur,
      houter, hprefix, hno⟩
    have hguard := k67GuardOk_constructive_witness
    rcases hguard with ⟨gstart, gcur, gnext, glen, gn1, gl1, gn7,
      hcleanOuter, hlen14, hzeroNonce, hl1, hommers⟩
    rcases hcleanOuter with ⟨hclean, houterG⟩
    rcases hclean with ⟨hprefix15, hitem1, hitem7, hitem14, hdecode14⟩
    have hdet := EvmAsm.Codegen.RlpListNthItemSAsm.strictListPayload_deterministic
      houter houterG
    have hstart : startOff = gstart := hdet.1
    rw [hstart] at hprefix
    obtain ⟨nn, ll, hrest⟩ :=
      EvmAsm.Codegen.RlpListNthItemSAsm.strictNthItem_extends_prefix
        hitem14 hprefix hile
    obtain ⟨n, l, hdec⟩ :=
      EvmAsm.Codegen.RlpListNthItemSAsm.strictNthItem_head hrest
    exact hno ⟨n, l, hdec⟩
  · have hnotinit :
        ¬ EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec.k67InitFailedPure
          (0 : Word) k67HeaderBytesLiteral k67HeaderBytesLiteral.length
          (by decide) := by
      unfold EvmAsm.Codegen.HeaderValidatePostMergeLoopSpec.k67InitFailedPure
      decide
    exact hnotinit hinit
end EvmAsm.Codegen.HeaderValidatePostMergeCorrespondenceBridge
