/-
  EvmAsm.Rv64.SAsm.FnFlatAmbientDemo

  Witness for the **ambient-preserving flat-contract adapter**
  (`Fn.retSpecFlatAmbient`, bead evm-asm-l0w4a): flatten the multi-read
  demo leaf `multiReadFn` — a leaf `Fn.retSpecFlat` CANNOT flatten,
  because its pre/post pin the ambient to the two read-only input
  buffers (`A = bytesRegion a0 bs0 ** bytesRegion a1 bs1`,
  `region = Region.empty`) rather than `empAssertion`.

  `multiReadFlat_spec` is the §5-shaped flat callee contract: entered at
  `base` with any aligned return address in `ra`, it returns to `ra`
  with the writable window pinned to the dword sum of the two ambient
  inputs, BOTH inputs untouched, and the register file forgotten to
  ownership — every conjunct derived from the leaf's own `Fn` post
  through the adapter's faithfulness hypothesis (nothing weakened,
  nothing invented).
-/

import EvmAsm.Rv64.SAsm.FnFlat
import EvmAsm.Rv64.SAsm.MultiRead

namespace EvmAsm.Rv64.SAsm

namespace FnFlatAmbientDemo

open MultiRead

/-- The flat, ambient-preserving contract of the multi-read demo leaf:
    `[a0..a0+8)` and `[a1..a1+8)` ride through UNCHANGED as ordinary
    conjuncts, the window at `dst` ends as their dword sum. -/
theorem multiReadFlat_spec (a0 a1 dst ret base : Word)
    (bs0 bs1 : List (BitVec 8))
    (hrw : RwRegion.wf ⟨dst, 8⟩)
    (hro0 : Region.wf ⟨a0, bs0⟩) (hro1 : Region.wf ⟨a1, bs1⟩)
    (hbs0 : bs0.length = 8) (hbs1 : bs1.length = 8)
    (hne0 : a0 ≠ dst) (hne1 : a1 ≠ dst)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (rf : RegFile) (ws : List (BitVec 8)) (hws : ws.length = 8)
    (h10 : rf.get .x10 = a0) (h11 : rf.get .x11 = a1)
    (h12 : rf.get .x12 = dst) :
    cpsTripleWithin ((multiReadFn a0 a1 dst bs0 bs1).body.steps + 1) base ret
      (CodeReq.ofProg base ((multiReadFn a0 a1 dst bs0 bs1).programRet base))
      (((.x1 : Reg) ↦ᵣ ret) ** (regFileIs rf) ** bytesRegion dst ws **
        (bytesRegion a0 bs0 ** bytesRegion a1 bs1))
      (((.x1 : Reg) ↦ᵣ ret) **
        bytesRegion dst (dwordBytes (packBytes bs0 + packBytes bs1)) **
        (bytesRegion a0 bs0 ** bytesRegion a1 bs1) **
        regOwns exposedRegs) := by
  have had := Fn.retSpecFlatAmbient (multiReadFn a0 a1 dst bs0 bs1) base
    (multiReadFn_spec a0 a1 dst bs0 bs1 base hrw hro0 hro1 hbs0 hbs1
      hne0 hne1)
    (by
      rw [show (multiReadFn a0 a1 dst bs0 bs1).body.size = 4 from rfl]
      decide)
    ret halign rf ws (bytesRegion a0 bs0 ** bytesRegion a1 bs1)
    (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
    (show ws.length = 8 from hws)
    ⟨h10, h11, h12, rfl⟩
    (Q := bytesRegion dst (dwordBytes (packBytes bs0 + packBytes bs1)) **
      (bytesRegion a0 bs0 ** bytesRegion a1 bs1) ** regOwns exposedRegs)
    (fun _rf' _ws' _A' hpost => hpost.2.2)
    (fun rf' ws' _hlen' hpost' hp hh => by
      obtain ⟨_h12', hws', _hA⟩ := hpost'
      rw [hws',
        show ((multiReadFn a0 a1 dst bs0 bs1).rw.base : Word) = dst from rfl]
        at hh
      have hh1 := sepConj_mono_left (sepConj_mono_left (fun h hr => by
        rw [regFileIs_eq_regAtoms,
          regAtoms_eq_regAtomsOf rf' exposedRegs (by decide)] at hr
        exact regAtomsOf_to_regOwns _ _ h hr)) hp hh
      xperm_hyp hh1)
  rw [show ((multiReadFn a0 a1 dst bs0 bs1).rw.base : Word) = dst from rfl,
      show (multiReadFn a0 a1 dst bs0 bs1).region.bytes
        = ([] : List (BitVec 8)) from rfl,
      bytesRegion_nil] at had
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [sepConj_emp_right']
      xperm_hyp hp)
    (fun h hq => by
      rw [sepConj_emp_right'] at hq
      xperm_hyp hq)
    had

#print axioms multiReadFlat_spec

end FnFlatAmbientDemo

end EvmAsm.Rv64.SAsm
