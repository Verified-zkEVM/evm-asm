/-
  EvmAsm.Rv64.SAsm.KeccakStep

  The machine-level seam for the concrete ZisK Keccak-f accelerator.  This
  deliberately proves only the inline `CSRS 0x800` instruction and its
  two-instruction return wrapper; the hash bridge's flat 69-instruction
  program remains emitted exactly as-is.
-/

import EvmAsm.Rv64.SAsm.AccelStep

namespace EvmAsm.Rv64
namespace SAsm

/-- The 25 little-endian dwords read by `csrs 0x800` from a state window. -/
def keccakDwords (ws : List (BitVec 8)) (k : Nat) : List Word :=
  (List.range 25).map fun i => wsDword ws (k + 8 * i)

/-- The byte image written back by the concrete Keccak-f accelerator. -/
def keccakBytes (ws : List (BitVec 8)) (k : Nat) : List (BitVec 8) :=
  (Accel.keccakF (keccakDwords ws k)).flatMap dwordBytes

@[simp] theorem length_keccakDwords (ws : List (BitVec 8)) (k : Nat) :
    (keccakDwords ws k).length = 25 := by
  simp [keccakDwords]

@[simp] theorem length_keccakBytes (ws : List (BitVec 8)) (k : Nat) :
  (keccakBytes ws k).length = 200 := by
  rw [keccakBytes, length_flatMap_dwordBytes, Accel.keccakF_length]

private theorem csrsValid_keccak (s : MachineState) (rs1 : Reg) :
    s.csrsValid 0x800 rs1 = MachineState.validDwordRange (s.getReg rs1) 25 := rfl

private theorem csrsWrite_keccak (s : MachineState) (rs1 : Reg) :
    s.csrsWrite 0x800 rs1 =
      (s.getReg rs1, Accel.keccakF (s.readWords (s.getReg rs1) 25)) := rfl

/-- One inline `csrs 0x800, rs1` step, with the state window decoded from the
    entry bytes and the post written back as concrete `Accel.keccakF` bytes.
    The only preconditions are the fixed 200-byte aligned scratch resource
    and the exposed register containing its offset. -/
theorem csrs_keccak_spec_within
    (base : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff : Nat) (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 200 ≤ len) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.singleton base (.CSRS 0x800 rs1))
      ((regFileIs rf) ** bytesRegion B ws)
      ((regFileIs rf) ** bytesRegion B
        (setBytes ws pOff (keccakBytes ws pOff))) := by
  apply csrs_step_spec_within 0x800 rs1 base B ws rf pOff
    (Accel.keccakF (keccakDwords ws pOff)) h8p
  · rw [Accel.keccakF_length]
    rw [hwslen]
    exact hpfit
  · intro R s hPR
    rw [sepConj_assoc'] at hPR
    have hregs : s.getReg rs1 = rf.get rs1 :=
      holdsFor_regFileIs_getReg hPR hrs1
    have hMem := hPR
    rw [sepConj_left_comm] at hMem
    have hsrs1 : s.getReg rs1 = B + BitVec.ofNat 64 pOff := by
      rw [hregs, hp]
    have hvrange :
        MachineState.validDwordRange (B + BitVec.ofNat 64 pOff) 25 = true :=
      validDwordRange_of_window hb8 hvalid h8p (by omega)
    have hread : s.readWords (B + BitVec.ofNat 64 pOff) 25 =
        keccakDwords ws pOff := by
      rw [holdsFor_bytesRegion_readWords hMem 25 pOff h8p (by omega)]
      rfl
    constructor
    · rw [csrsValid_keccak, hsrs1]
      exact hvrange
    · rw [csrsWrite_keccak, hsrs1, hread]
/-- The inline Keccak step followed by the ordinary return epilogue. -/
theorem csrs_keccak_ret_spec
    (entry : Word) (rs1 : Reg) (hrs1 : Reg.isExposed rs1 = true)
    (B : Word) (len : Nat) (ws : List (BitVec 8)) (rf : RegFile)
    (hwslen : ws.length = len)
    (hb8 : B.toNat % 8 = 0)
    (hvalid : ∀ j, j < len → isValidMemAddr (B + BitVec.ofNat 64 j) = true)
    (pOff : Nat) (hp : rf.get rs1 = B + BitVec.ofNat 64 pOff)
    (h8p : 8 ∣ pOff) (hpfit : pOff + 200 ≤ len)
    (A : Assertion) (hA : A.pcFree)
    (ret : Word) (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 2 entry ret
      (CodeReq.ofProg entry (csrsRetProgram 0x800 rs1))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B ws) ** A))
      ((.x1 ↦ᵣ ret) ** (((regFileIs rf) ** bytesRegion B
        (setBytes ws pOff (keccakBytes ws pOff))) ** A)) :=
  csrs_ret_spec_of_step
    (csrs_keccak_spec_within entry rs1 hrs1 B len ws rf hwslen hb8 hvalid
      pOff hp h8p hpfit)
    A hA ret halign

/-- The proof-only snapshot handle for a concrete Keccak-f step.  It is useful
    to structured proofs of the bridge, but does not replace the inline CSRS
    in `HashBridgeProg`. -/
def keccakPre (B : Word) (rs1 : Reg) (pOff : Nat) : Reach :=
  fun rf _ _ => rf.get rs1 = B + BitVec.ofNat 64 pOff

def keccakPost (pOff : Nat) :
    RegFile → List (BitVec 8) → Assertion → Reach :=
  fun rf₀ ws₀ A₀ rf ws A =>
    rf = rf₀ ∧ A = A₀ ∧ ws = setBytes ws₀ pOff (keccakBytes ws₀ pOff)

theorem keccakHandle_sound (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff : Nat) (h8p : 8 ∣ pOff) (hpfit : pOff + 200 ≤ len) :
    ∀ (rf₀ : RegFile) (ws₀ : List (BitVec 8)) (A₀ : Assertion),
      ws₀.length = len → A₀.pcFree →
      keccakPre B rs1 pOff rf₀ ws₀ A₀ →
      ∀ ret : Word, (ret &&& ~~~(1 : Word)) = ret →
      cpsTripleWithin 2 entry ret
        (CodeReq.ofProg entry (csrsRetProgram 0x800 rs1))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (Reach.exact rf₀ ws₀ A₀))
        ((.x1 ↦ᵣ ret) ** asrtM ro ⟨B, len⟩
          (keccakPost pOff rf₀ ws₀ A₀)) := by
  intro rf₀ ws₀ A₀ hlen hApc hpre ret halign
  have hcore := csrs_keccak_ret_spec entry rs1 hrs1 B len ws₀ rf₀ hlen
    hrw.1 hrw.2.2 pOff hpre h8p hpfit
    (A₀ ** bytesRegion ro.base ro.bytes)
    (pcFree_sepConj hApc (bytesRegion_pcFree _ _)) ret halign
  refine cpsTripleWithin_weaken (fun hq hh => ?_) (fun hq hh => ?_) hcore
  · rw [show asrtM ro ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀)
        = (asrtOf ⟨B, len⟩ (Reach.exact rf₀ ws₀ A₀)
          ** bytesRegion ro.base ro.bytes) from rfl, sepConj_comm'] at hh
    rw [sepConj_comm']
    refine sepConj_mono_left (fun hq' hh' => ?_) hq hh
    rw [← sepConj_assoc']
    refine sepConj_mono_left (fun hq'' hh'' => ?_) hq' hh'
    obtain ⟨rf, ws', A, -, -, ⟨rfl, rfl, rfl⟩, hsts⟩ := hh''
    exact hsts
  · rw [show asrtM ro ⟨B, len⟩ (keccakPost pOff rf₀ ws₀ A₀)
        = (asrtOf ⟨B, len⟩ (keccakPost pOff rf₀ ws₀ A₀)
          ** bytesRegion ro.base ro.bytes) from rfl, sepConj_comm']
    rw [sepConj_comm'] at hh
    refine sepConj_mono_left (fun hq' hh' => ?_) hq hh
    rw [← sepConj_assoc'] at hh'
    refine sepConj_mono_left (fun hq'' hh'' => ?_) hq' hh'
    exact ⟨rf₀, _, A₀, by rw [length_setBytes]; exact hlen,
      hApc, ⟨rfl, rfl, rfl⟩, hh''⟩

def keccakHandle (entry : Word) (rs1 : Reg)
    (hrs1 : Reg.isExposed rs1 = true)
    (ro : Region) (B : Word) (len : Nat)
    (hrw : (RwRegion.mk B len).wf)
    (pOff : Nat) (h8p : 8 ∣ pOff) (hpfit : pOff + 200 ≤ len) : FnHandleS where
  entry := entry
  code := CodeReq.ofProg entry (csrsRetProgram 0x800 rs1)
  nSteps := 2
  region := ro
  rw := ⟨B, len⟩
  pre := keccakPre B rs1 pOff
  post := keccakPost pOff
  sound := keccakHandle_sound entry rs1 hrs1 ro B len hrw pOff h8p hpfit

end SAsm
end EvmAsm.Rv64
