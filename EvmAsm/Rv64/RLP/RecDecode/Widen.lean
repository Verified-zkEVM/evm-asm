/-
  EvmAsm.Rv64.RLP.RecDecode.Widen

  `FnHandleS.widenPrefix`: repackage a snapshot callee verified against its
  own writable window `⟨b + k, n⟩` as a callee over the caller's window
  `⟨b, k + n⟩` whose first `k` bytes (the caller's frame) ride across the
  call untouched.  This is `FnHandle.widenRw` transported to snapshot
  handles: the widening prefix is not a ghost parameter of the handle but
  *the entry window's own first `k` bytes*, which is exactly what a call
  site inside a loop — whose frame contents differ per iteration — needs.

  Requirements: the callee's `pre` must not read the window (true of every
  register-argument calling convention), and the windows must be
  dword-aligned/multiple as usual.
-/

import EvmAsm.Rv64.RLP.RecDecode.Contract
import EvmAsm.Rv64.SAsm.HandleWiden

namespace EvmAsm.Rv64
namespace SAsm

open EvmAsm.EL.RLP (Byte)

/-- An exact reach is a window of the exact reach on its own suffix. -/
theorem Reach.exact_as_window (rf₀ : RegFile) (ws₀ : List (BitVec 8))
    (A₀ : Assertion) (k : Nat) (hk : k ≤ ws₀.length) :
    Reach.exact rf₀ ws₀ A₀
      = Reach.window (ws₀.take k) [] (ws₀.length - k)
          (Reach.exact rf₀ (ws₀.drop k) A₀) := by
  funext rf ws A
  apply propext
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨ws.drop k, by rw [List.length_drop], by
      rw [List.append_nil, List.take_append_drop], rfl, rfl, rfl⟩
  · rintro ⟨win, hwl, hws, rfl, rfl, rfl⟩
    refine ⟨rfl, ?_, rfl⟩
    rw [hws, List.append_nil, List.take_append_drop]

/-- Snapshot analogue of `FnHandle.widenRw`. -/
def FnHandleS.widenPrefix (h : FnHandleS) (b : Word) (k : Nat)
    (hbase : h.rw.base = b + BitVec.ofNat 64 k)
    (hk8 : 8 ∣ k) (hn8 : 8 ∣ h.rw.len)
    (hpre : ∀ (rf : RegFile) (ws ws' : List (BitVec 8)) (A : Assertion),
      h.pre rf ws A → h.pre rf ws' A) : FnHandleS where
  entry := h.entry
  code := h.code
  nSteps := h.nSteps
  region := h.region
  rw := ⟨b, k + h.rw.len⟩
  pre := h.pre
  post := fun rf₀ ws₀ A₀ rf ws A =>
    ws.take k = ws₀.take k
    ∧ h.post rf₀ (ws₀.drop k) A₀ rf (ws.drop k) A
  sound := by
    intro rf₀ ws₀ A₀ hlen hpc hpre₀ ret halign
    have hlen' : ws₀.length = k + h.rw.len := hlen
    have hdlen : (ws₀.drop k).length = h.rw.len := by
      rw [List.length_drop]
      omega
    have htlen : (ws₀.take k).length = k := by
      rw [List.length_take]
      omega
    have hinner := h.sound rf₀ (ws₀.drop k) A₀ hdlen hpc
      (hpre rf₀ ws₀ (ws₀.drop k) A₀ hpre₀) ret halign
    have hframe := cpsTripleWithin_frameR
      (bytesRegion b (ws₀.take k) **
        bytesRegion (h.rw.base + BitVec.ofNat 64 h.rw.len) [])
      (pcFree_sepConj (bytesRegion_pcFree _ _) (bytesRegion_pcFree _ _))
      hinner
    have hwbase : h.rw.base = (b : Word) + BitVec.ofNat 64
        (ws₀.take k).length := by
      rw [htlen, hbase]
    have hexact : Reach.exact rf₀ ws₀ A₀
        = Reach.window (ws₀.take k) [] h.rw.len
            (Reach.exact rf₀ (ws₀.drop k) A₀) := by
      rw [Reach.exact_as_window rf₀ ws₀ A₀ k (by omega),
        show ws₀.length - k = h.rw.len from by omega]
    have hwin := asrtM_window h.region ⟨b, k + h.rw.len⟩ h.rw
      (ws₀.take k) [] (Reach.exact rf₀ (ws₀.drop k) A₀)
      hwbase (by rw [htlen]; simp) (by rw [htlen]; exact hk8) hn8
    have hwinPost := asrtM_window h.region ⟨b, k + h.rw.len⟩ h.rw
      (ws₀.take k) [] (h.post rf₀ (ws₀.drop k) A₀)
      hwbase (by rw [htlen]; simp) (by rw [htlen]; exact hk8) hn8
    refine cpsTripleWithin_weaken ?_ ?_ hframe
    · intro hp hh
      rw [hexact, hwin,
        ← sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
          (asrtM h.region h.rw (Reach.exact rf₀ (ws₀.drop k) A₀))
          (bytesRegion b (ws₀.take k) **
            bytesRegion (h.rw.base + BitVec.ofNat 64 h.rw.len) [])] at hh
      exact hh
    · intro hp hh
      rw [sepConj_assoc' ((.x1 : Reg) ↦ᵣ ret)
          (asrtM h.region h.rw (h.post rf₀ (ws₀.drop k) A₀))
          (bytesRegion b (ws₀.take k) **
            bytesRegion (h.rw.base + BitVec.ofNat 64 h.rw.len) []),
        ← hwinPost] at hh
      have hweak : ∀ rf ws A,
          Reach.window (ws₀.take k) [] h.rw.len
            (h.post rf₀ (ws₀.drop k) A₀) rf ws A →
          (ws.take k = ws₀.take k
            ∧ h.post rf₀ (ws₀.drop k) A₀ rf (ws.drop k) A) := by
        rintro rf ws A ⟨win, hwl, hws, hpost⟩
        have htk : ws.take k = ws₀.take k := by
          rw [hws, List.append_nil,
            List.take_append_of_le_length (by rw [htlen]),
            List.take_of_length_le (by rw [htlen])]
        have hdr : ws.drop k = win := by
          rw [hws, List.append_nil]
          exact List.drop_left' htlen
        exact ⟨htk, hdr ▸ hpost⟩
      exact sepConj_mono_right (asrtM_mono hweak) hp hh

end SAsm
end EvmAsm.Rv64
