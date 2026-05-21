/-
  EvmAsm.Evm64.SMod.Compose.ResultSignFixPCFree

  PC-free helpers for SMOD result-sign-fix postconditions.
-/

import EvmAsm.Evm64.SDiv.Compose.ResultSignFixPCFree
import EvmAsm.Evm64.SMod.Compose.ResultSignFixView

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Evm64.SDiv.Compose (resultSignFixPost)

theorem resultSignFixPost_smodResultSign_pcFree
    {sp dividendTop limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
      limb0 limb1 limb2 limb3).pcFree := by
  exact EvmAsm.Evm64.SDiv.Compose.resultSignFixPost_pcFree

instance pcFreeInst_resultSignFixPost_smodResultSign
    (sp dividendTop limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (resultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
        limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPost_smodResultSign_pcFree⟩

theorem resultSignFixPost_smodResultSign_zero_pcFree
    {sp dividendTop : Word} :
    (resultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
      0 0 0 0).pcFree := by
  exact resultSignFixPost_smodResultSign_pcFree

instance pcFreeInst_resultSignFixPost_smodResultSign_zero
    (sp dividendTop : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (resultSignFixPost sp (dividendTop >>> (63 : BitVec 6).toNat)
        0 0 0 0) :=
  ⟨resultSignFixPost_smodResultSign_zero_pcFree⟩

end EvmAsm.Evm64.SMod.Compose
