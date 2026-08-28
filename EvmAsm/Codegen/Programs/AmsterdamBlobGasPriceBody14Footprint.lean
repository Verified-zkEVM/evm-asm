/- x0-freedom for the Body14 round footprint (#12851).  Kept in a sibling
   module so the large emitted-round proof remains within the file-size cap. -/
import EvmAsm.Codegen.Programs.AmsterdamBlobGasPriceBody14Spec

namespace EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Codegen
open EvmAsm.Codegen.HeaderValidateExcessBlobGasSpec
open EvmAsm.Codegen.AmsterdamBlobGasPrice

set_option maxRecDepth 8000

private theorem x0Free_sepConj {P Q : Assertion}
    (hP : x0FreeAssertion P) (hQ : x0FreeAssertion Q) :
    x0FreeAssertion (P ** Q) := by
  intro h hh
  obtain ⟨h1, h2, hd, hu, hp, hq⟩ := hh
  have h1x := hP h1 hp
  have h2x := hQ h2 hq
  rw [← hu]
  simp [PartialState.union, h1x, h2x]

private theorem x0Free_regIs {r : Reg} {v : Word} (hr : r ≠ .x0) :
    x0FreeAssertion (regIs r v) := by
  intro h hh
  rw [hh]
  simp [PartialState.singletonReg, Ne.symm hr]

private theorem x0Free_memIs {a v : Word} :
    x0FreeAssertion (memIs a v) := by
  intro h hh
  rw [hh.1]
  rfl

private theorem x0Free_regOwn {r : Reg} (hr : r ≠ .x0) :
    x0FreeAssertion (regOwn r) := by
  intro h hh
  obtain ⟨v, hv⟩ := hh
  exact x0Free_regIs hr h hv

private theorem x0Free_regOwns {rs : List Reg}
    (hrs : ∀ r ∈ rs, r ≠ .x0) :
    x0FreeAssertion (regOwns rs) := by
  induction rs with
  | nil =>
      intro h hh
      rw [hh]
      rfl
  | cons r rs ih =>
      simp only [regOwns_cons]
      exact x0Free_sepConj (x0Free_regOwn (hrs r (by simp)))
        (ih (fun r' hr' => hrs r' (by simp [hr'])))

private theorem x0Free_frameSlotsSaved (frame : FrameDesc)
    (newSp : Word) (vals : Reg → Word) :
    x0FreeAssertion (frameSlotsSaved frame newSp vals) := by
  induction frame with
  | nil =>
      intro h hh
      rw [hh]
      rfl
  | cons p rest ih =>
      simpa only [frameSlotsSaved_cons] using
        x0Free_sepConj x0Free_memIs ih

private theorem x0Free_cellsOf (base : Word) (ws : List Word) :
    x0FreeAssertion (cellsOf base ws) := by
  induction ws generalizing base with
  | nil =>
      intro h hh
      rw [hh]
      rfl
  | cons w ws ih =>
      simpa only [cellsOf_cons] using
        x0Free_sepConj x0Free_memIs (ih (base + 8))

theorem taylorRoundFootprint_x0Free
    (newSp excess outPtr iVal AB PB : Word) (vals : Reg → Word)
    (accC prodC sumC : List Word) (FR : Assertion)
    (hFR : x0FreeAssertion FR) :
    x0FreeAssertion (taylorRoundFootprint newSp excess outPtr iVal AB PB vals
      accC prodC sumC FR) := by
  unfold taylorRoundFootprint
  simp only [regOwns, sepConj_emp_right']
  have htemp : x0FreeAssertion
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31) := by
    exact x0Free_sepConj (x0Free_regOwn (r := .x5) (by decide))
      (x0Free_sepConj (x0Free_regOwn (r := .x6) (by decide))
        (x0Free_sepConj (x0Free_regOwn (r := .x7) (by decide))
          (x0Free_sepConj (x0Free_regOwn (r := .x28) (by decide))
            (x0Free_sepConj (x0Free_regOwn (r := .x29) (by decide))
              (x0Free_sepConj (x0Free_regOwn (r := .x30) (by decide))
                (x0Free_regOwn (r := .x31) (by decide)))))))
  apply x0Free_sepConj
  · exact x0Free_regIs (r := .x2) (by decide)
  · apply x0Free_sepConj
    · exact x0Free_regIs (r := .x1) (by decide)
    · apply x0Free_sepConj
      · exact x0Free_regIs (r := .x10) (by decide)
      · apply x0Free_sepConj
        · exact x0Free_regIs (r := .x11) (by decide)
        · apply x0Free_sepConj
          · exact x0Free_regIs (r := .x8) (by decide)
          · apply x0Free_sepConj
            · exact x0Free_regIs (r := .x9) (by decide)
            · apply x0Free_sepConj
              · exact x0Free_regIs (r := .x18) (by decide)
              · apply x0Free_sepConj
                · exact x0Free_regIs (r := .x19) (by decide)
                · apply x0Free_sepConj
                  · exact x0Free_regIs (r := .x20) (by decide)
                  · apply x0Free_sepConj
                    · exact x0Free_regIs (r := .x21) (by decide)
                    · apply x0Free_sepConj
                      · exact x0Free_regIs (r := .x22) (by decide)
                      · apply x0Free_sepConj
                        · exact htemp
                        · apply x0Free_sepConj
                          · exact x0Free_frameSlotsSaved _ _ _
                          · apply x0Free_sepConj
                            · exact x0Free_cellsOf _ _
                            · apply x0Free_sepConj
                              · exact x0Free_cellsOf _ _
                              · apply x0Free_sepConj
                                · exact x0Free_cellsOf _ _
                                · exact hFR

#print axioms taylorRoundFootprint_x0Free

end EvmAsm.Codegen.AmsterdamBlobGasPriceBody14Spec
