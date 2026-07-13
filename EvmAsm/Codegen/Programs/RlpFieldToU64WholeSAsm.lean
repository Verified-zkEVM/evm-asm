import EvmAsm.Codegen.Programs.RlpFieldToU64FinishSAsm

namespace EvmAsm.Codegen.RlpFieldToU64SAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.Rv64.SAsm

theorem allJoinedResult_to_restoreReady
    (newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat) : ∀ h,
    (allJoinedResult newSp listBase oldOffset oldLen saved bytes listLen index **
      savedFrame newSp outer) h →
    allRestoreReady newSp newSp listBase oldOffset oldLen outer saved bytes
      listLen index h := by
  intro h hp
  obtain ⟨h1, h2, hd, hu, hj, hsf⟩ := hp
  unfold allJoinedResult at hj
  unfold allRestoreReady
  rcases hj with hs | hf
  · left
    exact joinedResult_to_restoreReady newSp newSp listBase outer saved bytes
      listLen index h ⟨h1, h2, hd, hu, hs, hsf⟩
  · right
    exact failureResult_to_restoreReady newSp newSp listBase oldOffset oldLen outer
      saved bytes listLen index h ⟨h1, h2, hd, hu, hf, hsf⟩

#print axioms allJoinedResult_to_restoreReady

theorem dispatchAndRestore
    (spOuter newSp listBase oldOffset oldLen : Word) (outer : Saved)
    (saved : EvmAsm.Codegen.RlpListNthItemSAsm.Saved)
    (bytes : List (BitVec 8)) (listLen index : Nat)
    (hs0 : saved.s0 = listBase)
    (hsalign : listBase.toNat % 8 = 0)
    (hslack : listLen + 9 ≤ bytes.length)
    (hover : listBase.toNat + bytes.length < 2 ^ 64)
    (hvalid : ∀ k, k < bytes.length →
      isValidByteAccess (listBase + BitVec.ofNat 64 k) = true)
    (hnewSp : newSp = spOuter + signExtend12 (-32 : BitVec 12))
    (hret : outer.ra &&& ~~~(1 : Word) = outer.ra) :
    let tailSteps := (7 + (1 + (7 * (2 ^ 64 - 1) + 11))) + 5
    cpsTripleWithin ((1 + tailSteps) + 5) (B + 48) outer.ra code
      ((((.x1 ↦ᵣ (B + 48)) **
        listCallResult newSp listBase offsetCell lengthCell oldOffset oldLen saved
          bytes listLen index) ** (saved.s1 ↦ₘ (0 : Word))) **
        savedFrame newSp outer)
      (allReturned spOuter newSp listBase oldOffset oldLen outer saved bytes
        listLen index) := by
  dsimp
  have hd0 := listDispatchToJoin newSp listBase oldOffset oldLen saved bytes
    listLen index hs0 hsalign hslack hover hvalid
  have hd := cpsTripleWithin_frameR (savedFrame newSp outer)
    (by unfold savedFrame; pcf) hd0
  have hd' := cpsTripleWithin_weaken (fun _ hp => hp)
    (allJoinedResult_to_restoreReady newSp listBase oldOffset oldLen outer saved
      bytes listLen index) hd
  have hr := restoreAll spOuter newSp listBase oldOffset oldLen outer saved bytes
    listLen index hnewSp hret
  exact cpsTripleWithin_seq_perm_same_cr (fun _ hp => hp) hd' hr

#print axioms dispatchAndRestore

end EvmAsm.Codegen.RlpFieldToU64SAsm
