/-
  EvmAsm.Evm64.SMod.Compose.ResultSignFixPCFree

  PC-free helpers for SMOD result-sign-fix postconditions.
-/

module

public import EvmAsm.Evm64.SMod.Compose.ResultSignFixView

@[expose] public section

namespace EvmAsm.Evm64.SMod.Compose

theorem smodResultSignFixPost_smodResultSign_pcFree
    {sp dividendTop limb0 limb1 limb2 limb3 : Word} :
    (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
      limb0 limb1 limb2 limb3).pcFree := by
  exact smodResultSignFixPost_pcFree

instance pcFreeInst_smodResultSignFixPost_smodResultSign
    (sp dividendTop limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
        limb0 limb1 limb2 limb3) :=
  ⟨smodResultSignFixPost_smodResultSign_pcFree⟩

theorem smodResultSignFixPost_smodResultSign_zero_pcFree
    {sp dividendTop : Word} :
    (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
      0 0 0 0).pcFree := by
  exact smodResultSignFixPost_smodResultSign_pcFree

instance pcFreeInst_smodResultSignFixPost_smodResultSign_zero
    (sp dividendTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodResultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
        0 0 0 0) :=
  ⟨smodResultSignFixPost_smodResultSign_zero_pcFree⟩

end EvmAsm.Evm64.SMod.Compose
