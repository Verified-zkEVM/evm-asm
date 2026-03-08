/-
  EvmAsm.Rv32.SyscallSpecs

  CPS specifications for the HALT and WRITE macro instructions,
  proved by composing generalized per-instruction specs via structural rules
  (cpsTriple_seq, cpsTriple_seq_halt, frame embedding).
-/

import EvmAsm.Rv32.Basic
import EvmAsm.Rv32.Instructions
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.GenericSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.SpecDb
import Std.Tactic.BVDecide

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Section 1: Memory Buffer Assertion
-- ============================================================================

/-- Memory buffer: consecutive words at addr, addr+4, addr+8, ... -/
def memBufferIs : Addr → List Word → Assertion
  | _, [] => empAssertion
  | addr, w :: ws => (addr ↦ₘ w) ** memBufferIs (addr + 4) ws

theorem pcFree_memBufferIs (addr : Addr) (words : List Word) :
    (memBufferIs addr words).pcFree := by
  induction words generalizing addr with
  | nil => exact pcFree_emp
  | cons w ws ih => exact pcFree_sepConj (pcFree_memIs addr w) (ih (addr + 4))

/-- If memBufferIs holds, then readWords returns those words. -/
theorem readWords_of_holdsFor_memBufferIs {addr : Addr} {words : List Word}
    {s : MachineState}
    (h : (memBufferIs addr words).holdsFor s) :
    s.readWords addr words.length = words := by
  induction words generalizing addr with
  | nil => rfl
  | cons w ws ih =>
    simp only [memBufferIs] at h
    have hmem : s.getMem addr = w :=
      (holdsFor_memIs addr w s).mp (holdsFor_sepConj_elim_left h)
    have hrest := holdsFor_sepConj_elim_right h
    simp only [List.length_cons, MachineState.readWords]
    rw [hmem, ih hrest]

-- ============================================================================
-- Section 1b: readBytes ↔ memBufferIs Infrastructure
-- ============================================================================

/-- If memBufferIs holds, then getMem at each word offset returns the corresponding word. -/
theorem getMem_of_holdsFor_memBufferIs {addr : Addr} {words : List Word}
    {s : MachineState}
    (h : (memBufferIs addr words).holdsFor s) (k : Nat) (hk : k < words.length) :
    s.getMem (addr + BitVec.ofNat 32 (4 * k)) = words[k]'hk := by
  induction words generalizing addr k with
  | nil => simp at hk
  | cons w ws ih =>
    simp only [memBufferIs] at h
    cases k with
    | zero =>
      simp only [Nat.mul_zero, List.getElem_cons_zero]
      have : addr + BitVec.ofNat 32 0 = addr := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [this]; exact (holdsFor_memIs addr w s).mp (holdsFor_sepConj_elim_left h)
    | succ k' =>
      have hk' : k' < ws.length := by simp [List.length_cons] at hk; omega
      simp only [List.getElem_cons_succ]
      have : addr + BitVec.ofNat 32 (4 * (k' + 1)) = addr + 4 + BitVec.ofNat 32 (4 * k') := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [this]; exact ih (holdsFor_sepConj_elim_right h) k' hk'

/-- readBytes of 4 bytes at an aligned address equals the 4 extractBytes of the word. -/
theorem readBytes_4_of_getMem {addr : Addr} {w : Word} {s : MachineState}
    (hmem : s.getMem addr = w) (halign : addr &&& 3#32 = 0#32) :
    s.readBytes addr 4 = [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3] := by
  simp only [MachineState.readBytes, MachineState.getByte, alignToWord, byteOffset]
  have h0 : (addr &&& ~~~3#32) = addr := by bv_decide
  have h1 : ((addr + 1) &&& ~~~3#32) = addr := by bv_decide
  have h2 : ((addr + 1 + 1) &&& ~~~3#32) = addr := by bv_decide
  have h3 : ((addr + 1 + 1 + 1) &&& ~~~3#32) = addr := by bv_decide
  rw [h0, h1, h2, h3, hmem]
  have h0o : (addr &&& 3#32).toNat = 0 := by rw [halign]; rfl
  have h1a : ((addr + 1) &&& 3#32) = 1#32 := by bv_decide
  have h1o : ((addr + 1) &&& 3#32).toNat = 1 := by rw [h1a]; rfl
  have h2a : ((addr + 1 + 1) &&& 3#32) = 2#32 := by bv_decide
  have h2o : ((addr + 1 + 1) &&& 3#32).toNat = 2 := by rw [h2a]; rfl
  have h3a : ((addr + 1 + 1 + 1) &&& 3#32) = 3#32 := by bv_decide
  have h3o : ((addr + 1 + 1 + 1) &&& 3#32).toNat = 3 := by rw [h3a]; rfl
  rw [h0o, h1o, h2o, h3o]

/-- Adding 4 to an aligned address preserves alignment. -/
theorem aligned_add_4 {addr : Addr} (halign : addr &&& 3#32 = 0#32) :
    (addr + 4) &&& 3#32 = 0#32 := by bv_decide

/-- readBytes splits into prefix and suffix. -/
theorem readBytes_append (s : MachineState) (addr : Addr) (m n : Nat) :
    s.readBytes addr (m + n) = s.readBytes addr m ++ s.readBytes (addr + BitVec.ofNat 32 m) n := by
  induction m generalizing addr with
  | zero =>
    simp only [Nat.zero_add, MachineState.readBytes, List.nil_append]
    congr 1; apply BitVec.eq_of_toNat_eq; simp
  | succ k ih =>
    simp only [Nat.succ_add, MachineState.readBytes, List.cons_append]; congr 1
    rw [ih (addr + 1)]; congr 1; congr 1
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- readBytes of a word-aligned buffer equals flatMap extractByte of the words. -/
theorem readBytes_of_words {addr : Addr} {words : List Word} {s : MachineState}
    (hmem : ∀ (k : Nat) (hk : k < words.length), s.getMem (addr + BitVec.ofNat 32 (4 * k)) = words[k]'hk)
    (halign : addr &&& 3#32 = 0#32) :
    s.readBytes addr (4 * words.length) =
      words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3]) := by
  induction words generalizing addr with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_cons]
    rw [show 4 * (ws.length + 1) = 4 + 4 * ws.length from by omega]
    rw [readBytes_append]
    congr 1
    · have h0 := hmem 0 (Nat.zero_lt_succ _)
      simp only [Nat.mul_zero, List.getElem_cons_zero] at h0
      have : addr + BitVec.ofNat 32 0 = addr := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [this] at h0
      exact readBytes_4_of_getMem h0 halign
    · rw [show (BitVec.ofNat 32 4 : BitVec 32) = (4 : BitVec 32) from rfl]
      have hmem' : ∀ (k : Nat) (hk : k < ws.length),
          s.getMem (addr + 4 + BitVec.ofNat 32 (4 * k)) = ws[k]'hk := by
        intro k hk
        have := hmem (k + 1) (by simp [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at this
        have haddr_eq : addr + 4 + BitVec.ofNat 32 (4 * k) = addr + BitVec.ofNat 32 (4 * (k + 1)) := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [haddr_eq]; exact this
      exact ih hmem' (aligned_add_4 halign)

/-- Taking n elements from a longer readBytes gives readBytes n. -/
theorem readBytes_take (s : MachineState) (addr : Addr) (n m : Nat) (h : n ≤ m) :
    (s.readBytes addr m).take n = s.readBytes addr n := by
  induction n generalizing addr m with
  | zero => simp [MachineState.readBytes]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      simp only [MachineState.readBytes, List.take_succ_cons]; congr 1
      exact ih (addr + 1) m' (by omega)

-- ============================================================================
-- Section 1c: Separation Logic Rearrangement Helpers
-- ============================================================================

/-- Swap elements 1 and 2 of a right-associative chain: A ** B ** C → B ** A ** C. -/
private theorem swap12_assertion (A B C : Assertion) :
    ∀ h, (A ** B ** C) h → (B ** A ** C) h :=
  fun h hab =>
    sepConj_mono_right (fun h' hca => (sepConj_comm C A h').mp hca) h
      ((sepConj_assoc B C A h).mp ((sepConj_comm A (B ** C) h).mp hab))

/-- Pull element from position 5 to position 1: A ** B ** C ** D ** E ** F → E ** A ** B ** C ** D ** F. -/
private theorem pullFifth (A B C D E F : Assertion) :
    ∀ h, (A ** B ** C ** D ** E ** F) h → (E ** A ** B ** C ** D ** F) h :=
  fun h hab =>
    swap12_assertion A E (B ** C ** D ** F) h
    (sepConj_mono_right (fun h' => swap12_assertion B E (C ** D ** F) h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion C E (D ** F) h'') h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => sepConj_mono_right (fun h''' => swap12_assertion D E F h''') h'') h') h hab)))

/-- Push element from position 1 to position 5: E ** A ** B ** C ** D ** F → A ** B ** C ** D ** E ** F. -/
private theorem pushFifth (A B C D E F : Assertion) :
    ∀ h, (E ** A ** B ** C ** D ** F) h → (A ** B ** C ** D ** E ** F) h :=
  fun h hab =>
    sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => sepConj_mono_right (fun h''' => swap12_assertion E D F h''') h'') h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion E C (D ** F) h'') h') h
    (sepConj_mono_right (fun h' => swap12_assertion E B (C ** D ** F) h') h
    (swap12_assertion E A (B ** C ** D ** F) h hab)))

/-- Pull 5th element to front at holdsFor level (within (P ** R)). -/
theorem holdsFor_pullFifth {A B C D E F R : Assertion} {s : MachineState}
    (h : ((A ** B ** C ** D ** E ** F) ** R).holdsFor s) :
    ((E ** A ** B ** C ** D ** F) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pullFifth A B C D E F h1 hh1, hh2⟩

/-- Push element from front back to 5th position at holdsFor level (within (P ** R)). -/
theorem holdsFor_pushFifth {A B C D E F R : Assertion} {s : MachineState}
    (h : ((E ** A ** B ** C ** D ** F) ** R).holdsFor s) :
    ((A ** B ** C ** D ** E ** F) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pushFifth A B C D E F h1 hh1, hh2⟩

-- ============================================================================
-- Section 2: appendPublicValues Infrastructure
-- ============================================================================

namespace PartialState

/-- appendPublicValues preserves compatibility for partial states
    that don't own publicValues. -/
theorem CompatibleWith_appendPublicValues {h : PartialState} {s : MachineState}
    {bytes : List (BitVec 8)}
    (hcompat : h.CompatibleWith s) (hnone : h.publicValues = none) :
    h.CompatibleWith (s.appendPublicValues bytes) := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => by rw [MachineState.getReg_appendPublicValues]; exact hr r v hv,
         fun a v hv => by rw [MachineState.getMem_appendPublicValues]; exact hm a v hv,
         fun a i hv => by rw [MachineState.code_appendPublicValues]; exact hc a i hv,
         fun v hv => by rw [MachineState.pc_appendPublicValues]; exact hpc v hv,
         fun v hv => by rw [hnone] at hv; exact absurd hv (by simp),
         fun v hv => by rw [MachineState.privateInput_appendPublicValues]; exact hpi v hv⟩

end PartialState

/-- If (publicValuesIs oldPV ** R).holdsFor s, then
    (publicValuesIs (oldPV ++ words) ** R).holdsFor (s.appendPublicValues words).
    R is automatically publicValues-free by disjointness with publicValuesIs. -/
theorem holdsFor_sepConj_publicValuesIs_appendPublicValues
    {oldPV bytes : List (BitVec 8)} {R : Assertion} {s : MachineState}
    (hPR : ((publicValuesIs oldPV) ** R).holdsFor s) :
    ((publicValuesIs (oldPV ++ bytes)) ** R).holdsFor (s.appendPublicValues bytes) := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [publicValuesIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own publicValues (from disjointness)
  have hpv2 : h2.publicValues = none := by
    rcases hdisj.2.2.2.2.1 with h | h
    · simp [PartialState.singletonPublicValues] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPublicValues (oldPV ++ bytes)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, Or.inr hpv2, hdisj.2.2.2.2.2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPublicValues (oldPV ++ bytes) compatible with s.appendPublicValues bytes
  have hc1' : (PartialState.singletonPublicValues (oldPV ++ bytes)).CompatibleWith
      (s.appendPublicValues bytes) := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPublicValues] at hr,
            fun a w ha => by simp [PartialState.singletonPublicValues] at ha,
            fun a i hi => by simp [PartialState.singletonPublicValues] at hi,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => ?_,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw⟩
    simp only [PartialState.singletonPublicValues] at hw
    rw [Option.some.injEq] at hw; subst hw
    rw [MachineState.publicValues_appendPublicValues]
    exact congrArg (· ++ bytes)
      ((PartialState.CompatibleWith_singletonPublicValues oldPV s).mp hc1)
  -- h2 compatible with s.appendPublicValues bytes
  have hc2' : h2.CompatibleWith (s.appendPublicValues bytes) :=
    PartialState.CompatibleWith_appendPublicValues hc2 hpv2
  exact ⟨(PartialState.singletonPublicValues (oldPV ++ bytes)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPublicValues (oldPV ++ bytes), h2, hdisj', rfl, rfl, hh2⟩

-- ============================================================================
-- Section 2b: dropPrivateInput Infrastructure
-- ============================================================================

namespace PartialState

/-- Dropping bytes from privateInput preserves compatibility for partial states
    that don't own privateInput. -/
theorem CompatibleWith_dropPrivateInput {h : PartialState} {s : MachineState}
    {n : Nat}
    (hcompat : h.CompatibleWith s) (hnone : h.privateInput = none) :
    h.CompatibleWith { s with privateInput := s.privateInput.drop n } := by
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => hr r v hv,
         fun a v hv => hm a v hv,
         fun a i hv => hc a i hv,
         fun v hv => hpc v hv,
         fun v hv => hpv v hv,
         fun v hv => by rw [hnone] at hv; exact absurd hv (by simp)⟩

end PartialState

/-- If (privateInputIs allBytes ** R).holdsFor s, then
    (privateInputIs (allBytes.drop n) ** R).holdsFor {s with privateInput := s.privateInput.drop n}.
    R is automatically privateInput-free by disjointness with privateInputIs. -/
theorem holdsFor_sepConj_privateInputIs_drop
    {allBytes : List (BitVec 8)} {n : Nat} {R : Assertion} {s : MachineState}
    (hPR : ((privateInputIs allBytes) ** R).holdsFor s) :
    ((privateInputIs (allBytes.drop n)) ** R).holdsFor
      { s with privateInput := s.privateInput.drop n } := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [privateInputIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own privateInput (from disjointness)
  have hpi2 : h2.privateInput = none := by
    rcases hdisj.2.2.2.2.2 with h | h
    · simp [PartialState.singletonPrivateInput] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPrivateInput (allBytes.drop n)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2.1, Or.inr hpi2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPrivateInput (allBytes.drop n) compatible with modified state
  have hc1' : (PartialState.singletonPrivateInput (allBytes.drop n)).CompatibleWith
      { s with privateInput := s.privateInput.drop n } := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPrivateInput] at hr,
            fun a w ha => by simp [PartialState.singletonPrivateInput] at ha,
            fun a i hi => by simp [PartialState.singletonPrivateInput] at hi,
            fun w hw => by simp [PartialState.singletonPrivateInput] at hw,
            fun w hw => by simp [PartialState.singletonPrivateInput] at hw,
            fun w hw => ?_⟩
    simp only [PartialState.singletonPrivateInput] at hw
    rw [Option.some.injEq] at hw; subst hw
    show s.privateInput.drop n = allBytes.drop n
    congr 1
    exact (PartialState.CompatibleWith_singletonPrivateInput allBytes s).mp hc1
  -- h2 compatible with modified state
  have hc2' : h2.CompatibleWith { s with privateInput := s.privateInput.drop n } :=
    PartialState.CompatibleWith_dropPrivateInput hc2 hpi2
  exact ⟨(PartialState.singletonPrivateInput (allBytes.drop n)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPrivateInput (allBytes.drop n), h2, hdisj', rfl, rfl, hh2⟩

-- ============================================================================
-- Section 2c: writeBytesAsWords Memory Update Infrastructure
-- ============================================================================

namespace PartialState

/-- writeBytesAsWords preserves compatibility for partial states
    that don't own the target memory addresses. -/
theorem CompatibleWith_writeBytesAsWords {h : PartialState} {s : MachineState}
    {base : Addr} {bytes : List (BitVec 8)}
    (hcompat : h.CompatibleWith s)
    (hnone : ∀ (k : Nat), k < (bytes.length + 3) / 4 → h.mem (base + BitVec.ofNat 32 (4 * k)) = none) :
    h.CompatibleWith (s.writeBytesAsWords base bytes) := by
  match bytes with
  | [] =>
    unfold MachineState.writeBytesAsWords
    exact hcompat
  | b :: bs =>
    unfold MachineState.writeBytesAsWords
    have h0 := hnone 0 (by simp)
    simp at h0
    apply CompatibleWith_writeBytesAsWords (base := base + 4) (bytes := (b :: bs).drop 4)
    · exact CompatibleWith_setMem hcompat h0
    · intro k hk
      have hlen_drop : ((b :: bs).drop 4).length = bs.length + 1 - 4 := by
        simp [List.length_drop]
      have : k + 1 < ((b :: bs).length + 3) / 4 := by
        rw [hlen_drop] at hk
        have : (b :: bs).length = bs.length + 1 := by simp
        rw [this]
        omega
      have hval := hnone (k + 1) this
      have haddr : base + 4 + BitVec.ofNat 32 (4 * k) = base + BitVec.ofNat 32 (4 * (k + 1)) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [haddr]; exact hval
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

end PartialState

/-- Helper: unfold one step of bytesToWords on 4+ elements. -/
private theorem bytesToWords_cons4 (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    bytesToWords (b0 :: b1 :: b2 :: b3 :: rest) =
    bytesToWordLE [b0, b1, b2, b3] :: bytesToWords rest := by
  simp [bytesToWords]

/-- Helper: unfold one step of writeBytesAsWords on 4+ elements. -/
private theorem writeBytesAsWords_cons4 (s : MachineState) (base : Addr)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    s.writeBytesAsWords base (b0 :: b1 :: b2 :: b3 :: rest) =
    (s.setMem base (bytesToWordLE [b0, b1, b2, b3])).writeBytesAsWords (base + 4) rest := by
  simp [MachineState.writeBytesAsWords]

/-- If (memBufferIs base oldWords ** R).holdsFor s and we write bytes of the same total size,
    then (memBufferIs base (bytesToWords bytes) ** R).holdsFor (s.writeBytesAsWords base bytes). -/
theorem holdsFor_sepConj_memBufferIs_writeBytesAsWords
    {base : Addr} {oldWords : List Word} {bytes : List (BitVec 8)} {R : Assertion}
    {s : MachineState}
    (hlen : bytes.length = 4 * oldWords.length)
    (hPR : ((memBufferIs base oldWords) ** R).holdsFor s) :
    ((memBufferIs base (bytesToWords bytes)) ** R).holdsFor (s.writeBytesAsWords base bytes) := by
  -- Generalize R for the induction to work with different frames
  suffices h : ∀ (oldWords' : List Word) (R' : Assertion) (base' : Addr) (bytes' : List (BitVec 8))
      (s' : MachineState),
      bytes'.length = 4 * oldWords'.length →
      ((memBufferIs base' oldWords') ** R').holdsFor s' →
      ((memBufferIs base' (bytesToWords bytes')) ** R').holdsFor (s'.writeBytesAsWords base' bytes') from
    h oldWords R base bytes s hlen hPR
  intro oldWords'
  induction oldWords' with
  | nil =>
    intro R' base' bytes' s' hlen' hPR'
    have : bytes' = [] := by cases bytes' <;> simp_all
    subst this
    simp [memBufferIs]
    exact hPR'
  | cons w ws ih =>
    intro R' base' bytes' s' hlen' hPR'
    -- bytes has at least 4 elements
    have hlen4 : bytes'.length ≥ 4 := by simp [List.length_cons] at hlen'; omega
    obtain ⟨b0, b1, b2, b3, rest, hbytes, hrest_len⟩ : ∃ b0 b1 b2 b3 rest,
        bytes' = b0 :: b1 :: b2 :: b3 :: rest ∧ rest.length = 4 * ws.length := by
      match bytes', hlen' with
      | b0 :: b1 :: b2 :: b3 :: rest, hlen' =>
        exact ⟨b0, b1, b2, b3, rest, rfl, by simp [List.length_cons] at hlen'; omega⟩
    subst hbytes
    -- Rewrite goal using the unfold lemmas
    rw [bytesToWords_cons4, writeBytesAsWords_cons4]
    -- Goal is now: ((memBufferIs base' (btwLE :: bytesToWords rest)) ** R').holdsFor (setMem.wbaw rest)
    -- which after memBufferIs unfold becomes:
    -- (((base' ↦ₘ btwLE) ** memBufferIs (base'+4) (bytesToWords rest)) ** R').holdsFor ...
    change (((base' ↦ₘ bytesToWordLE [b0, b1, b2, b3]) ** memBufferIs (base' + 4) (bytesToWords rest)) ** R').holdsFor _
    -- hPR' : (((base' ↦ₘ w) ** memBufferIs (base'+4) ws) ** R').holdsFor s'
    change (((base' ↦ₘ w) ** memBufferIs (base' + 4) ws) ** R').holdsFor s' at hPR'
    -- Reassociate: (base' ↦ₘ w) ** (memBufferIs ws ** R')
    have hPR'' := holdsFor_sepConj_assoc.mp hPR'
    -- Update memory at base': (base' ↦ₘ newWord) ** (memBufferIs ws ** R')
    let newWord := bytesToWordLE [b0, b1, b2, b3]
    have h1 : ((base' ↦ₘ newWord) ** (memBufferIs (base' + 4) ws ** R')).holdsFor
        (s'.setMem base' newWord) :=
      holdsFor_sepConj_memIs_setMem hPR''
    -- Reassociate: ((base' ↦ₘ newWord) ** memBufferIs ws) ** R'
    have h1c := holdsFor_sepConj_assoc.mpr h1
    -- pull_second: memBufferIs ws ** ((base' ↦ₘ newWord) ** R')
    have h1d := holdsFor_sepConj_pull_second.mp h1c
    -- Apply IH with R'' = (base' ↦ₘ newWord) ** R'
    have h3 := ih ((base' ↦ₘ newWord) ** R') (base' + 4) rest (s'.setMem base' newWord) hrest_len h1d
    -- h3 : (memBufferIs (base'+4) (bytesToWords rest) ** ((base' ↦ₘ newWord) ** R')).holdsFor ...
    -- pull_second back: ((base' ↦ₘ newWord) ** memBufferIs (base'+4) (bytesToWords rest)) ** R'
    exact holdsFor_sepConj_pull_second.mpr h3

-- ============================================================================
-- Section 3: Generalized Instruction Specs
-- ============================================================================

/-- LW spec for any code memory: loads mem[rs1 + sext(offset)] into rd. -/
@[spec_gen] theorem lw_spec_gen (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((addr ↦ᵢ .LW rd rs1 offset) ** (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) :=
  generic_lw_spec rd rs1 v_addr v_old mem_val offset addr hrd_ne_x0 hvalid

/-- SLTIU spec for any code memory (rd == rs1 case):
    rd := (v <u sext(imm)) ? 1 : 0 -/
@[spec_gen] theorem sltiu_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTIU rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .SLTIU rd rd imm) ** (rd ↦ᵣ (if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word)))) :=
  generic_1reg_spec (.SLTIU rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- XORI spec for any code memory (rd == rs1 case):
    rd := v ^^^ sext(imm) -/
@[spec_gen] theorem xori_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .XORI rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .XORI rd rd imm) ** (rd ↦ᵣ (v ^^^ signExtend12 imm))) :=
  generic_1reg_spec (.XORI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SRL spec for any code memory (rd = rs1 case):
    rd := rd >>> (rs2.toNat % 32) -/
@[spec_gen] theorem srl_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRL rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SRL rd rd rs2) ** (rd ↦ᵣ (v1 >>> (v2.toNat % 32))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SRL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLL spec for any code memory (rd = rs1 case):
    rd := rd <<< (rs2.toNat % 32) -/
@[spec_gen] theorem sll_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLL rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SLL rd rd rs2) ** (rd ↦ᵣ (v1 <<< (v2.toNat % 32))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SLL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD spec for any code memory (rd = rs1 case):
    rd := rd + rs2 -/
@[spec_gen] theorem add_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ADD rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .ADD rd rd rs2) ** (rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.ADD rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB spec for any code memory (rd = rs1 case):
    rd := rd - rs2 -/
@[spec_gen] theorem sub_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SUB rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SUB rd rd rs2) ** (rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SUB rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- AND spec for any code memory (rd = rs1 case):
    rd := rd &&& rs2 -/
@[spec_gen] theorem and_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .AND rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .AND rd rd rs2) ** (rd ↦ᵣ (v1 &&& v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.AND rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- OR spec for any code memory (rd = rs1 case):
    rd := rd ||| rs2 -/
@[spec_gen] theorem or_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .OR rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .OR rd rd rs2) ** (rd ↦ᵣ (v1 ||| v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.OR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- XOR spec for any code memory (rd = rs1 case):
    rd := rd ^^^ rs2 -/
@[spec_gen] theorem xor_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .XOR rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .XOR rd rd rs2) ** (rd ↦ᵣ (v1 ^^^ v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.XOR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLTU spec for any code memory (rd = rs1 case):
    rd := if rd <u rs2 then 1 else 0 -/
@[spec_gen] theorem sltu_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTU rd rd rs2) ** (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((addr ↦ᵢ .SLTU rd rd rs2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SLTU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDI spec for any code memory (rd = rs1 case):
    rd := rd + signExtend12(imm) -/
@[spec_gen] theorem addi_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ADDI rd rd imm) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .ADDI rd rd imm) ** (rd ↦ᵣ (v + signExtend12 imm))) :=
  generic_1reg_spec (.ADDI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- LI spec for any code memory (not just a single-instruction loadProgram). -/
@[spec_gen] theorem li_spec_gen (rd : Reg) (v_old imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ imm)) :=
  generic_1reg_spec (.LI rd imm) rd v_old _ addr hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- LI spec for any code memory with regOwn (no v_old needed).
    Requires instrAt in pre/post since code is part of the machine state. -/
@[spec_gen] theorem li_spec_gen_own (rd : Reg) (imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .LI rd imm) ** regOwn rd)
      ((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ imm)) := by
  intro R hR s hPR hpc
  -- Decompose: ((instrAt ** regOwn) ** R).holdsFor s
  obtain ⟨h, hcompat, hPQ, hR_ps, hdisj, hunion, hpq, hrR⟩ := hPR
  obtain ⟨hI, hOwn, hdisjI, hunionI, hpI, hpOwn⟩ := hpq
  -- Extract existential from regOwn
  obtain ⟨v, hv⟩ := hpOwn
  -- Reconstruct with regIs instead of regOwn
  have hPR' : (((addr ↦ᵢ .LI rd imm) ** (rd ↦ᵣ v)) ** R).holdsFor s :=
    ⟨h, hcompat, hPQ, hR_ps, hdisj, hunion, ⟨hI, hOwn, hdisjI, hunionI, hpI, hv⟩, hrR⟩
  exact li_spec_gen rd v imm addr hrd_ne_x0 R hR s hPR' hpc

/-- ECALL halt spec: when x5 = 0, ECALL halts. -/
@[spec_gen] theorem ecall_halt_spec_gen (exitCode : Word) (addr : Addr) :
    cpsHaltTriple addr
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR s hPR hpc; subst hpc
  -- Extract code fetch and register values from precondition
  have hfetch : s.code s.pc = some .ECALL :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx5 : s.getReg .x5 = (0 : Word) :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  -- Witness: 0 steps, the current state s is already halted
  refine ⟨0, s, rfl, ?_, hPR⟩
  -- Show isHalted s = true
  simp only [isHalted, step_ecall_halt s hfetch hx5, Option.isNone]

/-- SW rs1 rs2 offset: mem[rs1 + sext(offset)] := rs2 (generalized for any CodeMem) -/
@[spec_gen] theorem sw_spec_gen (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((addr ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sw_spec rs1 rs2 v_addr v_data mem_old offset addr hvalid

/-- SW spec with memOwn (no mem_old needed).
    Requires instrAt in pre/post since code is part of the machine state. -/
@[spec_gen] theorem sw_spec_gen_own (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((addr ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hPR hpc
  -- Decompose ((instrAt ** regIs ** regIs ** memOwn) ** R).holdsFor s
  obtain ⟨h, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hI, hRest, hd1, hu1, hpI, hpRest⟩ := hpP
  obtain ⟨hR1, hRest2, hd2, hu2, hpR1, hpRest2⟩ := hpRest
  obtain ⟨hR2, hM, hd3, hu3, hpR2, hpM⟩ := hpRest2
  obtain ⟨v, hv⟩ := hpM
  -- Reconstruct with memIs instead of memOwn
  have hPR' : (((addr ↦ᵢ .SW rs1 rs2 offset) ** (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
    ((v_addr + signExtend12 offset) ↦ₘ v)) ** R).holdsFor s :=
    ⟨h, hcompat, h_P, h_R, hdisj, hunion,
     ⟨hI, hRest, hd1, hu1, hpI, ⟨hR1, hRest2, hd2, hu2, hpR1, ⟨hR2, hM, hd3, hu3, hpR2, hv⟩⟩⟩, hpR⟩
  exact sw_spec_gen rs1 rs2 v_addr v_data v offset addr hvalid R hR s hPR' hpc

/-- SW rs1 x0 offset: mem[rs1 + sext(offset)] := 0.
    Specialized version of sw_spec_gen for x0 (always reads as 0).
    Does not require (x0 ↦ᵣ 0) in pre/post. -/
@[spec_gen] theorem sw_x0_spec_gen (rs1 : Reg) (v_addr mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SW rs1 .x0 offset) ** (rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((addr ↦ᵢ .SW rs1 .x0 offset) ** (rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) :=
  generic_sw_x0_spec rs1 v_addr mem_old offset addr hvalid

-- ============================================================================
-- Section 4: Frame Embedding for cpsTriple
-- ============================================================================

/-- Frame on the right: if cpsTriple P → Q, then cpsTriple (P ** F) → (Q ** F). -/
theorem cpsTriple_frame_left (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

/-- Frame for cpsBranch: if cpsBranch P → Q_t | Q_f, then cpsBranch (P ** F) → (Q_t ** F) | (Q_f ** F). -/
theorem cpsBranch_frame_left (entry : Addr)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch entry P exit_t Q_t exit_f Q_f) :
    cpsBranch entry (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hcase⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, hcase.elim
    (fun ⟨hpc', hpost⟩ => Or.inl ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)
    (fun ⟨hpc', hpost⟩ => Or.inr ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)⟩

/-- Frame for cpsNBranch: if cpsNBranch P → exits, then cpsNBranch (P ** F) → exits with F. -/
theorem cpsNBranch_frame_left (entry : Addr)
    (P : Assertion) (exits : List (Addr × Assertion))
    (F : Assertion) (hF : F.pcFree)
    (h : cpsNBranch entry P exits) :
    cpsNBranch entry (P ** F) (exits.map fun (a, Q) => (a, Q ** F)) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, ⟨exit_, hmem, hpc', hpost⟩⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, ⟨(exit_.1, exit_.2 ** F),
    List.mem_map.mpr ⟨exit_, hmem, rfl⟩,
    hpc', holdsFor_sepConj_assoc.mpr hpost⟩⟩

/-- Frame for cpsNBranch on the right: if cpsNBranch P → exits, then cpsNBranch (F ** P) → exits with F. -/
theorem cpsNBranch_frame_right (entry : Addr)
    (P : Assertion) (exits : List (Addr × Assertion))
    (F : Assertion) (hF : F.pcFree)
    (h : cpsNBranch entry P exits) :
    cpsNBranch entry (F ** P) (exits.map fun (a, Q) => (a, F ** Q)) := by
  intro R hR s hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, ⟨exit_, hmem, hpc', hpost⟩⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hPFR hpc
  exact ⟨k, s', hstep, ⟨(exit_.1, F ** exit_.2),
    List.mem_map.mpr ⟨exit_, hmem, rfl⟩,
    hpc', holdsFor_sepConj_pull_second.mpr hpost⟩⟩

/-- Frame on the left: if cpsTriple P → Q, then cpsTriple (F ** P) → (F ** Q). -/
theorem cpsTriple_frame_right (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry P Q) :
    cpsHaltTriple entry (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hhalt, hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR' hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hpost⟩

/-- Frame on the left for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_right (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry P Q) :
    cpsHaltTriple entry (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hhalt, hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hPFR hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_pull_second.mpr hpost⟩

-- ============================================================================
-- Section 5: Generalized HALT spec (for arbitrary CodeMem)
-- ============================================================================

/-- HALT exitCode on arbitrary CodeMem, given fetch proofs for the 3 instructions.
    Uses regOwn (no old values needed).
    Requires instrAt for LI x5 0, LI x10 exitCode, ECALL. -/
theorem halt_spec_gen (exitCode : Word) (base : Addr) :
    cpsHaltTriple base
      ((base ↦ᵢ .LI .x5 0) ** ((base + 4) ↦ᵢ .LI .x10 exitCode) ** ((base + 8) ↦ᵢ .ECALL) **
       regOwn .x5 ** regOwn .x10)
      ((base ↦ᵢ .LI .x5 0) ** ((base + 4) ↦ᵢ .LI .x10 exitCode) ** ((base + 8) ↦ᵢ .ECALL) **
       (.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR s hPR hpc
  -- Extract regOwn existentials
  obtain ⟨h, hcompat, hP, hR_ps, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨h1, hRest1, hd1, hu1, hp1, hpRest1⟩ := hpP
  obtain ⟨h2, hRest2, hd2, hu2, hp2, hpRest2⟩ := hpRest1
  obtain ⟨h3, hRest3, hd3, hu3, hp3, hpRest3⟩ := hpRest2
  obtain ⟨h4, h5, hd4, hu4, hp4, hp5⟩ := hpRest3
  obtain ⟨v5, hv5⟩ := hp4
  obtain ⟨v10, hv10⟩ := hp5
  -- Reconstruct with regIs
  have hPR' : (((base ↦ᵢ .LI .x5 0) ** ((base + 4) ↦ᵢ .LI .x10 exitCode) ** ((base + 8) ↦ᵢ .ECALL) **
    (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10)) ** R).holdsFor s :=
    ⟨h, hcompat, hP, hR_ps, hdisj, hunion,
     ⟨h1, hRest1, hd1, hu1, hp1,
      ⟨h2, hRest2, hd2, hu2, hp2,
       ⟨h3, hRest3, hd3, hu3, hp3,
        ⟨h4, h5, hd4, hu4, hv5, hv10⟩⟩⟩⟩, hpR⟩
  -- Step 1: LI .x5 0 at base, framed with {instr2, instr3, reg_x10}
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LI .x10 exitCode) ** ((base + 8) ↦ᵢ .ECALL) ** (.x10 ↦ᵣ v10))
    (by pcFree) (li_spec_gen .x5 v5 0 base (by nofun))
  -- Step 2: LI .x10 exitCode at base+4, framed with {instr1, instr3, reg_x5=0}
  have s2_raw := li_spec_gen .x10 v10 exitCode (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 0) ** ((base + 8) ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word)))
    (by pcFree) s2_raw
  -- Step 3: ECALL halt at base+8, framed with {instr1, instr2}
  have s3 := cpsHaltTriple_frame_left _ _ _
    ((base ↦ᵢ .LI .x5 0) ** ((base + 4) ↦ᵢ .LI .x10 exitCode))
    (by pcFree) (ecall_halt_spec_gen exitCode (base + 8))
  -- Compose steps 1+2 via seq_with_perm
  have h12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1 s2
  -- Normalize h12's post and s3's pre to the same intermediate assertion
  let Qmid := ((base + 4) ↦ᵢ .LI .x10 exitCode) ** (.x10 ↦ᵣ exitCode) **
    (base ↦ᵢ .LI .x5 0) ** ((base + 8) ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (0 : Word))
  have h12' : cpsTriple base (base + 8) _ Qmid :=
    cpsTriple_consequence _ _ _ _ _ _
      (fun _ hp => hp) (fun _ hq => by xperm_hyp hq) h12
  have s3' : cpsHaltTriple (base + 8) Qmid _ :=
    cpsHaltTriple_consequence _ _ _ _ _
      (fun _ hp => by xperm_hyp hp) (fun _ hq => hq) s3
  -- Compose with halt step and apply final pre/post permutation
  exact (cpsHaltTriple_consequence _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq)
    (cpsTriple_seq_halt _ _ _ _ _ h12' s3')) R hR s hPR' hpc

-- ============================================================================
-- Section 5a: Combined store word spec (LI x6 val ;; SW x7 x6 offset)
-- ============================================================================

/-- Combined spec for "LI x6, val ;; SW x7, x6, offset":
    Stores val at mem[x7_val + sext(offset)], updates x6 to val.
    Proved by composing li_spec_gen and sw_spec_gen. -/
theorem storeWord_spec_gen (val : Word) (offset : BitVec 12)
    (x6_old x7_val mem_old : Word) (addr : Addr)
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple addr (addr + 8)
      ((addr ↦ᵢ .LI .x6 val) ** ((addr + 4) ↦ᵢ .SW .x7 .x6 offset) **
       (.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
      ((addr ↦ᵢ .LI .x6 val) ** ((addr + 4) ↦ᵢ .SW .x7 .x6 offset) **
       (.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  -- Normalize addr + 4 + 4 = addr + 8
  have ha : (addr + 4) + 4 = addr + 8 := by bv_omega
  -- Step 1: LI x6 val at addr
  have s1_raw := li_spec_gen .x6 x6_old val addr (by nofun)
  have s1 := cpsTriple_frame_left _ _ _ _
    (((addr + 4) ↦ᵢ .SW .x7 .x6 offset) **
     (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
    (by pcFree) s1_raw
  -- Step 2: SW x7 x6 offset at addr+4
  have s2_raw := sw_spec_gen .x7 .x6 x7_val val mem_old offset (addr + 4) hvalid
  rw [ha] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((addr ↦ᵢ .LI .x6 val))
    (by pcFree) s2_raw
  -- Compose
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s1 s2)

/-- Combined LI+SW spec with regOwn and memOwn (no x6_old or mem_old needed).
    Requires instrAt in pre/post since code is part of the machine state. -/
theorem storeWord_spec_gen_own (val : Word) (offset : BitVec 12)
    (x7_val : Word) (addr : Addr)
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple addr (addr + 8)
      ((addr ↦ᵢ .LI .x6 val) ** ((addr + 4) ↦ᵢ .SW .x7 .x6 offset) **
       regOwn .x6 ** (.x7 ↦ᵣ x7_val) ** memOwn (x7_val + signExtend12 offset))
      ((addr ↦ᵢ .LI .x6 val) ** ((addr + 4) ↦ᵢ .SW .x7 .x6 offset) **
       (.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  intro R hR s hPR hpc
  -- Decompose ((instrAt1 ** instrAt2 ** regOwn ** regIs ** memOwn) ** R).holdsFor s
  obtain ⟨h, hcompat, hP, hR_ps, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨h1, hRest1, hd1, hu1, hp1, hpRest1⟩ := hpP
  obtain ⟨h2, hRest2, hd2, hu2, hp2, hpRest2⟩ := hpRest1
  obtain ⟨h3, hRest3, hd3, hu3, hp3, hpRest3⟩ := hpRest2
  obtain ⟨h4, h5, hd4, hu4, hp4, hp5⟩ := hpRest3
  -- Extract existentials
  obtain ⟨x6_old, hx6⟩ := hp3
  obtain ⟨mem_old, hmem⟩ := hp5
  -- Reconstruct with regIs and memIs
  have hPR' : (((addr ↦ᵢ .LI .x6 val) ** ((addr + 4) ↦ᵢ .SW .x7 .x6 offset) **
    (.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old)) ** R).holdsFor s :=
    ⟨h, hcompat, hP, hR_ps, hdisj, hunion,
     ⟨h1, hRest1, hd1, hu1, hp1,
      ⟨h2, hRest2, hd2, hu2, hp2,
       ⟨h3, hRest3, hd3, hu3, hx6,
        ⟨h4, h5, hd4, hu4, hp4, hmem⟩⟩⟩⟩, hpR⟩
  exact storeWord_spec_gen val offset x6_old x7_val mem_old addr hvalid R hR s hPR' hpc

-- ============================================================================
-- Section 5b: ECALL HINT_READ specification
-- ============================================================================

/-- Pull element from position 4 to position 1: A ** B ** C ** D ** E → D ** A ** B ** C ** E. -/
private theorem pullFourth (A B C D E : Assertion) :
    ∀ h, (A ** B ** C ** D ** E) h → (D ** A ** B ** C ** E) h :=
  fun h hab =>
    swap12_assertion A D (B ** C ** E) h
    (sepConj_mono_right (fun h' => swap12_assertion B D (C ** E) h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion C D E h'') h') h hab))

/-- Push element from position 1 to position 4: D ** A ** B ** C ** E → A ** B ** C ** D ** E. -/
private theorem pushFourth (A B C D E : Assertion) :
    ∀ h, (D ** A ** B ** C ** E) h → (A ** B ** C ** D ** E) h :=
  fun h hab =>
    sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion D C E h'') h') h
    (sepConj_mono_right (fun h' => swap12_assertion D B (C ** E) h') h
    (swap12_assertion D A (B ** C ** E) h hab))

/-- Pull 4th element to front at holdsFor level. -/
theorem holdsFor_pullFourth {A B C D E R : Assertion} {s : MachineState}
    (h : ((A ** B ** C ** D ** E) ** R).holdsFor s) :
    ((D ** A ** B ** C ** E) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pullFourth A B C D E h1 hh1, hh2⟩

/-- Push element from front back to 4th position at holdsFor level. -/
theorem holdsFor_pushFourth {A B C D E R : Assertion} {s : MachineState}
    (h : ((D ** A ** B ** C ** E) ** R).holdsFor s) :
    ((A ** B ** C ** D ** E) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pushFourth A B C D E h1 hh1, hh2⟩

/-- Single ECALL step for HINT_READ (t0 = 0xF1).
    Precondition: x5 = 0xF1, x10 = bufAddr, x11 = nbytes,
                  privateInput = inputBytes, memory buffer at bufAddr = oldWords.
    Postcondition: same registers, privateInput = inputBytes.drop nbytes.toNat,
                   memory buffer = bytesToWords (inputBytes.take nbytes.toNat). -/
theorem ecall_hint_read_spec_gen (bufAddr nbytes : Word)
    (inputBytes : List (BitVec 8)) (oldWords : List Word) (addr : Addr)
    (hLen : nbytes.toNat ≤ inputBytes.length)
    (hNbytes : nbytes.toNat = 4 * oldWords.length) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs (inputBytes.drop nbytes.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat))) := by
  intro R hR s hPR hpc; subst hpc
  -- Extract code fetch and register values from precondition
  have hfetch : s.code s.pc = some .ECALL :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx5 : s.getReg .x5 = 0xF1#32 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hx10 : s.getReg .x10 = bufAddr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))
  have hx11 : s.getReg .x11 = nbytes :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))))
  have hpi : s.privateInput = inputBytes :=
    (holdsFor_privateInputIs _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right
          (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))))
  -- Sufficient input check
  have hsuff : (s.getReg .x11).toNat ≤ s.privateInput.length := by
    rw [hx11, hpi]; exact hLen
  -- Compute the next state
  let s_drop : MachineState := { s with privateInput := s.privateInput.drop (s.getReg .x11).toNat }
  let s_write := s_drop.writeBytesAsWords (s.getReg .x10) (s.privateInput.take (s.getReg .x11).toNat)
  let s_next := s_write.setPC (s.pc + 4)
  -- Witness: 1 step
  refine ⟨1, s_next, ?_, rfl, ?_⟩
  · -- stepN 1 s = some s_next
    show (step s).bind (stepN 0) = some s_next
    rw [step_ecall_hint_read s hfetch hx5 hsuff]; rfl
  · -- Postcondition
    -- The next state is:
    -- ({ s with privateInput := s.privateInput.drop nbytes.toNat }.writeBytesAsWords
    --    (s.getReg .x10) (s.privateInput.take nbytes.toNat)).setPC (s.pc + 4)
    -- which after rewriting with hx10, hx11, hpi becomes:
    -- ({ s with privateInput := inputBytes.drop nbytes.toNat }.writeBytesAsWords
    --    bufAddr (inputBytes.take nbytes.toNat)).setPC (s.pc + 4)

    -- Step A: Pull privateInputIs (5th element) to front, apply drop
    have h1 := holdsFor_pullFifth (A := (s.pc ↦ᵢ .ECALL))
      (B := (.x5 ↦ᵣ 0xF1#32)) (C := (.x10 ↦ᵣ bufAddr)) (D := (.x11 ↦ᵣ nbytes))
      (E := privateInputIs inputBytes) (F := memBufferIs bufAddr oldWords) hPR
    -- h1 : ((privateInputIs inputBytes ** instrAt ** x5 ** x10 ** x11 ** memBuf) ** R).holdsFor s

    -- Apply privateInput drop
    -- First, use holdsFor_sepConj_assoc to get (pI ** rest) form for the drop lemma
    have h1' := holdsFor_sepConj_assoc.mp h1
    -- h1' : (privateInputIs inputBytes ** ((instr ** x5 ** x10 ** x11 ** memBuf) ** R)).holdsFor s
    have h2' := @holdsFor_sepConj_privateInputIs_drop inputBytes nbytes.toNat _ s h1'
    -- h2' : (privateInputIs (inputBytes.drop nbytes.toNat) ** rest).holdsFor {s with pi.drop n}
    -- Reassociate back
    have h3 := holdsFor_sepConj_assoc.mpr h2'
    -- h3 : ((privateInputIs dropped ** (instr ** x5 ** x10 ** x11 ** memBuf)) ** R).holdsFor s_drop

    -- Step B: Push privateInputIs back to position, pull memBuf to front
    -- h3 has shape ((pI' ** (instr ** x5 ** x10 ** x11 ** memBuf)) ** R)
    -- We need to get memBuf to front.
    -- First push pI' into the chain:
    have h4 := holdsFor_pushFifth
      (A := (s.pc ↦ᵢ .ECALL))
      (B := (.x5 ↦ᵣ 0xF1#32))
      (C := (.x10 ↦ᵣ bufAddr))
      (D := (.x11 ↦ᵣ nbytes))
      (E := privateInputIs (inputBytes.drop nbytes.toNat))
      (F := memBufferIs bufAddr oldWords) h3
    -- h4 : ((instr ** x5 ** x10 ** x11 ** pI' ** memBuf) ** R).holdsFor s_drop

    -- Pull memBuf to front using pull_second repeatedly
    have hp1 := holdsFor_sepConj_pull_second.mp h4
    have hp2 := holdsFor_sepConj_pull_second.mp hp1
    have hp3 := holdsFor_sepConj_pull_second.mp hp2
    have hp4 := holdsFor_sepConj_pull_second.mp hp3
    have hp5 := holdsFor_sepConj_pull_second.mp hp4
    -- hp5 : (memBuf ** (pI' ** x11 ** x10 ** x5 ** instr ** R)).holdsFor s_drop

    -- Apply writeBytesAsWords lemma
    -- s_write = s_drop.writeBytesAsWords (s.getReg .x10) (s.privateInput.take (s.getReg .x11).toNat)
    -- = s_drop.writeBytesAsWords bufAddr (inputBytes.take nbytes.toNat) [by hx10, hpi, hx11]
    have hbytes_eq : s.privateInput.take (s.getReg .x11).toNat = inputBytes.take nbytes.toNat := by
      rw [hpi, hx11]
    have hbytes_len : (inputBytes.take nbytes.toNat).length = 4 * oldWords.length := by
      rw [List.length_take, Nat.min_eq_left hLen, hNbytes]

    have h5 : ((memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat)) **
      (privateInputIs (inputBytes.drop nbytes.toNat) ** (.x11 ↦ᵣ nbytes) ** (.x10 ↦ᵣ bufAddr) **
       (.x5 ↦ᵣ 0xF1#32) ** (s.pc ↦ᵢ .ECALL) ** R))).holdsFor
      ({ s with privateInput := s.privateInput.drop (s.getReg .x11).toNat }.writeBytesAsWords
        (s.getReg .x10) (s.privateInput.take (s.getReg .x11).toNat)) := by
      rw [hx10, hbytes_eq]
      have : { s with privateInput := s.privateInput.drop (s.getReg .x11).toNat } =
             { s with privateInput := s.privateInput.drop nbytes.toNat } := by
        rw [hx11]
      rw [this]
      exact holdsFor_sepConj_memBufferIs_writeBytesAsWords hbytes_len hp5

    -- Push memBuf back, pull instrAt to front
    have hq5 := holdsFor_sepConj_pull_second.mpr h5
    have hq4 := holdsFor_sepConj_pull_second.mpr hq5
    have hq3 := holdsFor_sepConj_pull_second.mpr hq4
    have hq2 := holdsFor_sepConj_pull_second.mpr hq3
    have hq1 := holdsFor_sepConj_pull_second.mpr hq2
    -- hq1 : ((instrAt ** x5 ** x10 ** x11 ** pI' ** memBuf') ** R).holdsFor s_write

    -- Step C: Apply setPC
    have hpcfree : ((s.pc ↦ᵢ .ECALL) ** (.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs (inputBytes.drop nbytes.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat))).pcFree :=
      pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_regIs _ _)
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
          (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))))
    exact holdsFor_pcFree_setPC (pcFree_sepConj hpcfree hR) _ _ hq1

-- ============================================================================
-- Section 5c: Generalized HINT_READ macro spec (LI x5 0xF1 ;; LI x10 buf ;; LI x11 n ;; ECALL)
-- ============================================================================

/-- HINT_READ bufAddr nbytes on arbitrary CodeMem (4-instruction macro).
    Uses regOwn (no old register values needed). -/
theorem hint_read_spec_gen (bufAddr nbytes_val : Word)
    (inputBytes : List (BitVec 8)) (oldWords : List Word) (base : Addr)
    (hLen : nbytes_val.toNat ≤ inputBytes.length)
    (hNbytes : nbytes_val.toNat = 4 * oldWords.length) :
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LI .x5 0xF1#32) ** ((base + 4) ↦ᵢ .LI .x10 bufAddr) **
       ((base + 8) ↦ᵢ .LI .x11 nbytes_val) ** ((base + 12) ↦ᵢ .ECALL) **
       regOwn .x5 ** regOwn .x10 ** regOwn .x11 **
       privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
      ((base ↦ᵢ .LI .x5 0xF1#32) ** ((base + 4) ↦ᵢ .LI .x10 bufAddr) **
       ((base + 8) ↦ᵢ .LI .x11 nbytes_val) ** ((base + 12) ↦ᵢ .ECALL) **
       (.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes_val) **
       privateInputIs (inputBytes.drop nbytes_val.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes_val.toNat))) := by
  intro R hR s hPR hpc
  -- Extract regOwn existentials
  obtain ⟨h, hcompat, hP, hR_ps, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨h1, hRest1, hd1, hu1, hp1, hpRest1⟩ := hpP
  obtain ⟨h2, hRest2, hd2, hu2, hp2, hpRest2⟩ := hpRest1
  obtain ⟨h3, hRest3, hd3, hu3, hp3, hpRest3⟩ := hpRest2
  obtain ⟨h4, hRest4, hd4, hu4, hp4, hpRest4⟩ := hpRest3
  obtain ⟨h5, hRest5, hd5, hu5, hp5, hpRest5⟩ := hpRest4
  obtain ⟨h6, hRest6, hd6, hu6, hp6, hpRest6⟩ := hpRest5
  obtain ⟨h7, hRest7, hd7, hu7, hp7, hpRest7⟩ := hpRest6
  obtain ⟨h8, h9, hd8, hu8, hp8, hp9⟩ := hpRest7
  obtain ⟨v5, hv5⟩ := hp5
  obtain ⟨v10, hv10⟩ := hp6
  obtain ⟨v11, hv11⟩ := hp7
  -- Reconstruct with regIs
  have hPR' : (((base ↦ᵢ .LI .x5 0xF1#32) ** ((base + 4) ↦ᵢ .LI .x10 bufAddr) **
     ((base + 8) ↦ᵢ .LI .x11 nbytes_val) ** ((base + 12) ↦ᵢ .ECALL) **
     (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
     privateInputIs inputBytes ** memBufferIs bufAddr oldWords) ** R).holdsFor s :=
    ⟨h, hcompat, hP, hR_ps, hdisj, hunion,
     ⟨h1, hRest1, hd1, hu1, hp1,
      ⟨h2, hRest2, hd2, hu2, hp2,
       ⟨h3, hRest3, hd3, hu3, hp3,
        ⟨h4, hRest4, hd4, hu4, hp4,
         ⟨h5, hRest5, hd5, hu5, hv5,
          ⟨h6, hRest6, hd6, hu6, hv10,
           ⟨h7, hRest7, hd7, hu7, hv11,
            ⟨h8, h9, hd8, hu8, hp8, hp9⟩⟩⟩⟩⟩⟩⟩⟩, hpR⟩
  -- Step 1: LI .x5 0xF1 at base
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LI .x10 bufAddr) ** ((base + 8) ↦ᵢ .LI .x11 nbytes_val) **
     ((base + 12) ↦ᵢ .ECALL) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
     privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
    (by apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))))))
    (li_spec_gen .x5 v5 0xF1#32 base (by nofun))
  -- Step 2: LI .x10 bufAddr at base+4
  have s2_raw := li_spec_gen .x10 v10 bufAddr (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 0xF1#32) ** ((base + 8) ↦ᵢ .LI .x11 nbytes_val) **
     ((base + 12) ↦ᵢ .ECALL) ** (.x5 ↦ᵣ 0xF1#32) ** (.x11 ↦ᵣ v11) **
     privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
    (by apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))))))
    s2_raw
  -- Step 3: LI .x11 nbytes_val at base+8
  have s3_raw := li_spec_gen .x11 v11 nbytes_val (base + 8) (by nofun)
  rw [show (base + 8 : Addr) + 4 = base + 12 from by bv_omega] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 0xF1#32) ** ((base + 4) ↦ᵢ .LI .x10 bufAddr) **
     ((base + 12) ↦ᵢ .ECALL) ** (.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) **
     privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
    (by apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))))))
    s3_raw
  -- Step 4: ECALL hint_read at base+12
  have s4_raw := ecall_hint_read_spec_gen bufAddr nbytes_val inputBytes oldWords (base + 12) hLen hNbytes
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 0xF1#32) ** ((base + 4) ↦ᵢ .LI .x10 bufAddr) **
     ((base + 8) ↦ᵢ .LI .x11 nbytes_val))
    (by apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_instrAt _ _)))
    s4_raw
  -- Compose
  have h12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1 s2
  have h123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) h12 s3
  have h1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) h123 s4
  exact (cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h1234) R hR s hPR' hpc

-- ============================================================================
-- Section 6: ECALL WRITE (public values) specification
-- ============================================================================

/-- Single ECALL step for WRITE to public values (fd = 13).
    Precondition: x5 = 0x02, x10 = 13, x11 = bufPtr, x12 = nbytes,
                  publicValues = oldPV, memory buffer at bufPtr = words.
    Postcondition: same registers, publicValues = oldPV ++ bytes, memory preserved.

    The WRITE syscall reads individual bytes from memory (matching SP1).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem ecall_write_public_spec_gen (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (addr : Addr)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((addr ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  intro R hR s hPR hpc; subst hpc
  -- Extract values from precondition
  have hfetch : s.code s.pc = some .ECALL :=
    (holdsFor_instrAt _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx5 : s.getReg .x5 = BitVec.ofNat 32 0x02 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hx10 : s.getReg .x10 = (13 : Word) :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))
  have hx11 : s.getReg .x11 = bufPtr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))))
  have hx12 : s.getReg .x12 = nbytes :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right
          (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))))
  have hpv : s.publicValues = oldPV :=
    (holdsFor_publicValuesIs _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right
          (holdsFor_sepConj_elim_right
            (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))))))
  have hmem_holdsFor : (memBufferIs bufPtr words).holdsFor s :=
    holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right
          (holdsFor_sepConj_elim_right
            (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))))
  -- Compute what readBytes returns
  have hmem_words : ∀ (k : Nat) (hk : k < words.length),
      s.getMem (bufPtr + BitVec.ofNat 32 (4 * k)) = words[k]'hk :=
    getMem_of_holdsFor_memBufferIs hmem_holdsFor
  have hreadBytes : s.readBytes bufPtr (4 * words.length) =
      words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3]) :=
    readBytes_of_words hmem_words hAligned
  have hreadBytes_take : (s.readBytes bufPtr (4 * words.length)).take nbytes.toNat =
      (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat :=
    by rw [hreadBytes]
  -- The WRITE syscall reads s.readBytes (s.getReg .x11) (s.getReg .x12).toNat
  -- = s.readBytes bufPtr nbytes.toNat  [by hx11, hx12]
  -- = (s.readBytes bufPtr (4 * words.length)).take nbytes.toNat  [by readBytes_take]
  -- = (flatMap...).take nbytes.toNat  [by hreadBytes_take]
  have hreadBytes_actual : s.readBytes (s.getReg .x11) (s.getReg .x12).toNat =
      (s.readBytes bufPtr (4 * words.length)).take nbytes.toNat := by
    rw [hx11, hx12]
    exact (readBytes_take s bufPtr nbytes.toNat (4 * words.length) hLen).symm
  -- step_ecall_write_public: step s = some ((s.appendPublicValues bytes).setPC (s.pc + 4))
  have hstep := step_ecall_write_public s hfetch hx5 hx10
  -- The appended bytes = s.readBytes bufPtr nbytes.toNat
  --   = (flatMap extractBytes words).take nbytes.toNat
  -- Witness: 1 step
  let s_append := s.appendPublicValues (s.readBytes (s.getReg .x11) (s.getReg .x12).toNat)
  let s_next := s_append.setPC (s.pc + 4)
  refine ⟨1, s_next, ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some s_next
    rw [hstep]; rfl
  · -- Postcondition
    -- The state changes: appendPublicValues then setPC
    -- Memory (memBufferIs) is unchanged by appendPublicValues and setPC
    -- Registers are unchanged by appendPublicValues and setPC
    -- publicValues changes from oldPV to oldPV ++ readBytes

    -- Step A: Pull publicValuesIs to front, apply append
    -- The assertion chain has 7 elements (instrAt ** x5 ** x10 ** x11 ** x12 ** pv ** memBuf)
    -- publicValuesIs is element 6. We need a "pull 6th" operation.
    -- Let's use pull_second repeatedly via the outer frame.
    have hp1 := holdsFor_sepConj_pull_second.mp hPR
    have hp2 := holdsFor_sepConj_pull_second.mp hp1
    have hp3 := holdsFor_sepConj_pull_second.mp hp2
    have hp4 := holdsFor_sepConj_pull_second.mp hp3
    have hp5 := holdsFor_sepConj_pull_second.mp hp4
    -- hp5 : ((pv ** memBuf) ** (x12 ** x11 ** x10 ** x5 ** instrAt ** R)).holdsFor s
    -- Assoc to get pv first:
    have hp6 := holdsFor_sepConj_assoc.mp hp5
    -- hp6 : (pv ** (memBuf ** (x12 ** x11 ** x10 ** x5 ** instrAt ** R))).holdsFor s

    -- Apply appendPublicValues
    -- Need to show the appended bytes match
    have hbytes_eq : s.readBytes (s.getReg .x11) (s.getReg .x12).toNat =
        (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat := by
      rw [hreadBytes_actual, hreadBytes_take]
    have hp7 : (publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) **
      (memBufferIs bufPtr words ** (.x12 ↦ᵣ nbytes) ** (.x11 ↦ᵣ bufPtr) **
       (.x10 ↦ᵣ (13 : Word)) ** (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (s.pc ↦ᵢ .ECALL) ** R)).holdsFor
      s_append := by
      show (publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) **
        (memBufferIs bufPtr words ** (.x12 ↦ᵣ nbytes) ** (.x11 ↦ᵣ bufPtr) **
         (.x10 ↦ᵣ (13 : Word)) ** (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (s.pc ↦ᵢ .ECALL) ** R)).holdsFor
        (s.appendPublicValues (s.readBytes (s.getReg .x11) (s.getReg .x12).toNat))
      rw [hbytes_eq]
      exact holdsFor_sepConj_publicValuesIs_appendPublicValues hp6

    -- Reassemble: push pv back to correct position
    have hq6 := holdsFor_sepConj_assoc.mpr hp7
    -- hq6 : ((pv' ** memBuf) ** (x12 ** x11 ** x10 ** x5 ** instrAt ** R)).holdsFor s_append
    have hq5 := holdsFor_sepConj_pull_second.mpr hq6
    have hq4 := holdsFor_sepConj_pull_second.mpr hq5
    have hq3 := holdsFor_sepConj_pull_second.mpr hq4
    have hq2 := holdsFor_sepConj_pull_second.mpr hq3
    have hq1 := holdsFor_sepConj_pull_second.mpr hq2
    -- hq1 : ((instrAt ** x5 ** x10 ** x11 ** x12 ** pv' ** memBuf) ** R).holdsFor s_append

    -- Apply setPC
    have hpcfree : ((s.pc ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) **
       memBufferIs bufPtr words).pcFree :=
      pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_regIs _ _)
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
          (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))))
    exact holdsFor_pcFree_setPC (pcFree_sepConj hpcfree hR) _ _ hq1

-- ============================================================================
-- Section 7: Generalized WRITE spec (for arbitrary CodeMem)
-- ============================================================================

/-- WRITE 13 bufPtr nbytes on arbitrary CodeMem, given fetch proofs for all 5 instructions.
    Uses regOwn (no old register values needed).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem write_public_spec_gen (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (base : Addr)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32) :
    cpsTriple base (base + 20)
      ((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 4) ↦ᵢ .LI .x10 13) **
       ((base + 8) ↦ᵢ .LI .x11 bufPtr) ** ((base + 12) ↦ᵢ .LI .x12 nbytes) **
       ((base + 16) ↦ᵢ .ECALL) **
       regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 4) ↦ᵢ .LI .x10 13) **
       ((base + 8) ↦ᵢ .LI .x11 bufPtr) ** ((base + 12) ↦ᵢ .LI .x12 nbytes) **
       ((base + 16) ↦ᵢ .ECALL) **
       (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  intro R hR s hPR hpc
  -- Extract regOwn existentials
  obtain ⟨h, hcompat, hP, hR_ps, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨h1, hRest1, hd1, hu1, hp1, hpRest1⟩ := hpP
  obtain ⟨h2, hRest2, hd2, hu2, hp2, hpRest2⟩ := hpRest1
  obtain ⟨h3, hRest3, hd3, hu3, hp3, hpRest3⟩ := hpRest2
  obtain ⟨h4, hRest4, hd4, hu4, hp4, hpRest4⟩ := hpRest3
  obtain ⟨h5, hRest5, hd5, hu5, hp5, hpRest5⟩ := hpRest4
  obtain ⟨h6, hRest6, hd6, hu6, hp6, hpRest6⟩ := hpRest5
  obtain ⟨h7, hRest7, hd7, hu7, hp7, hpRest7⟩ := hpRest6
  obtain ⟨h8, hRest8, hd8, hu8, hp8, hpRest8⟩ := hpRest7
  obtain ⟨h9, hRest9, hd9, hu9, hp9, hpRest9⟩ := hpRest8
  obtain ⟨h10, h11, hd10, hu10, hp10, hp11⟩ := hpRest9
  -- Extract register existentials from regOwn
  obtain ⟨v5, hv5⟩ := hp6
  obtain ⟨v10, hv10⟩ := hp7
  obtain ⟨v11, hv11⟩ := hp8
  obtain ⟨v12, hv12⟩ := hp9
  -- Reconstruct with regIs
  have hPR' : (((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 4) ↦ᵢ .LI .x10 13) **
     ((base + 8) ↦ᵢ .LI .x11 bufPtr) ** ((base + 12) ↦ᵢ .LI .x12 nbytes) **
     ((base + 16) ↦ᵢ .ECALL) **
     (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     publicValuesIs oldPV ** memBufferIs bufPtr words) ** R).holdsFor s :=
    ⟨h, hcompat, hP, hR_ps, hdisj, hunion,
     ⟨h1, hRest1, hd1, hu1, hp1,
      ⟨h2, hRest2, hd2, hu2, hp2,
       ⟨h3, hRest3, hd3, hu3, hp3,
        ⟨h4, hRest4, hd4, hu4, hp4,
         ⟨h5, hRest5, hd5, hu5, hp5,
          ⟨h6, hRest6, hd6, hu6, hv5,
           ⟨h7, hRest7, hd7, hu7, hv10,
            ⟨h8, hRest8, hd8, hu8, hv11,
             ⟨h9, hRest9, hd9, hu9, hv12,
              ⟨h10, h11, hd10, hu10, hp10, hp11⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩, hpR⟩
  -- Step 1: LI .x5 0x02 at base
  have s1_raw := li_spec_gen .x5 v5 (BitVec.ofNat 32 0x02) base (by nofun)
  have s1 := cpsTriple_frame_left _ _ _ _
    (((base + 4) ↦ᵢ .LI .x10 13) ** ((base + 8) ↦ᵢ .LI .x11 bufPtr) **
     ((base + 12) ↦ᵢ .LI .x12 nbytes) ** ((base + 16) ↦ᵢ .ECALL) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     publicValuesIs oldPV ** memBufferIs bufPtr words)
    (by
      apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)))))))))
    s1_raw
  -- Step 2: LI .x10 13 at base+4
  have s2_raw := li_spec_gen .x10 v10 (13 : Word) (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2_raw
  have s2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 8) ↦ᵢ .LI .x11 bufPtr) **
     ((base + 12) ↦ᵢ .LI .x12 nbytes) ** ((base + 16) ↦ᵢ .ECALL) **
     (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
     publicValuesIs oldPV ** memBufferIs bufPtr words)
    (by
      apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)))))))))
    s2_raw
  -- Step 3: LI .x11 bufPtr at base+8
  have s3_raw := li_spec_gen .x11 v11 bufPtr (base + 8) (by nofun)
  rw [show (base + 8 : Addr) + 4 = base + 12 from by bv_omega] at s3_raw
  have s3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 4) ↦ᵢ .LI .x10 13) **
     ((base + 12) ↦ᵢ .LI .x12 nbytes) ** ((base + 16) ↦ᵢ .ECALL) **
     (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x12 ↦ᵣ v12) **
     publicValuesIs oldPV ** memBufferIs bufPtr words)
    (by
      apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)))))))))
    s3_raw
  -- Step 4: LI .x12 nbytes at base+12
  have s4_raw := li_spec_gen .x12 v12 nbytes (base + 12) (by nofun)
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega] at s4_raw
  have s4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 4) ↦ᵢ .LI .x10 13) **
     ((base + 8) ↦ᵢ .LI .x11 bufPtr) ** ((base + 16) ↦ᵢ .ECALL) **
     (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) **
     publicValuesIs oldPV ** memBufferIs bufPtr words)
    (by
      apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
          (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
            (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)))))))))
    s4_raw
  -- Step 5: ECALL at base+16
  have s5_raw := ecall_write_public_spec_gen bufPtr nbytes oldPV words (base + 16) hLen hAligned
  rw [show (base + 16 : Addr) + 4 = base + 20 from by bv_omega] at s5_raw
  have s5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .LI .x5 (BitVec.ofNat 32 0x02)) ** ((base + 4) ↦ᵢ .LI .x10 13) **
     ((base + 8) ↦ᵢ .LI .x11 bufPtr) ** ((base + 12) ↦ᵢ .LI .x12 nbytes))
    (by
      apply pcFree_sepConj (pcFree_instrAt _ _) (pcFree_sepConj (pcFree_instrAt _ _)
        (pcFree_sepConj (pcFree_instrAt _ _) (pcFree_instrAt _ _))))
    s5_raw
  -- Compose: s1 ;; s2 ;; s3 ;; s4 ;; s5
  have h12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1 s2
  have h123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) h12 s3
  have h1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) h123 s4
  have h12345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) h1234 s5
  -- Apply final consequence to match pre/post
  exact (cpsTriple_consequence _ _ _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) h12345) R hR s hPR' hpc

/-- SLTU spec for 3 distinct registers:
    rd := (rs1 < rs2) ? 1 : 0, preserving rs1 and rs2 -/
@[spec_gen] theorem sltu_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTU rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .SLTU rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then 1 else 0))) :=
  generic_3reg_spec (.SLTU rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- OR spec for 3 distinct registers:
    rd := rs1 ||| rs2, preserving rs1 and rs2 -/
@[spec_gen] theorem or_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .OR rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .OR rd rs1 rs2) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 ||| v2))) :=
  generic_3reg_spec (.OR rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

-- ============================================================================
-- Section 10: Additional instruction specs for SHR proofs
-- ============================================================================

/-- ANDI spec for any code memory (rd ≠ rs1 case):
    rd := rs1 &&& sext(imm), preserving rs1 -/
@[spec_gen] theorem andi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ANDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .ANDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 &&& signExtend12 imm))) :=
  generic_2reg_spec (.ANDI rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SRLI spec for any code memory (rd == rs1 case):
    rd := rd >>> shamt -/
@[spec_gen] theorem srli_spec_gen_same (rd : Reg) (v : Word) (shamt : BitVec 5)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SRLI rd rd shamt) ** (rd ↦ᵣ v))
      ((addr ↦ᵢ .SRLI rd rd shamt) ** (rd ↦ᵣ (v >>> shamt.toNat))) :=
  generic_1reg_spec (.SRLI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLTIU spec for any code memory (rd ≠ rs1 case):
    rd := (rs1 <u sext(imm)) ? 1 : 0, preserving rs1 -/
@[spec_gen] theorem sltiu_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SLTIU rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .SLTIU rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.ult v1 (signExtend12 imm) then (1 : Word) else (0 : Word)))) :=
  generic_2reg_spec (.SLTIU rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDI spec for any code memory (rd ≠ rs1 case):
    rd := rs1 + sext(imm), preserving rs1 -/
@[spec_gen] theorem addi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .ADDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((addr ↦ᵢ .ADDI rd rs1 imm) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec (.ADDI rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB spec for any code memory (rd = rs2 case):
    rd := rs1 - rd, preserving rs1 -/
@[spec_gen] theorem sub_spec_gen_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((addr ↦ᵢ .SUB rd rs1 rd) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((addr ↦ᵢ .SUB rd rs1 rd) ** (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_2reg_spec (.SUB rd rs1 rd) rs1 rd v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- BNE spec for any code memory:
    Branch taken (v1 ≠ v2) → PC = addr + sext(offset)
    Branch not taken (v1 = v2) → PC = addr + 4 -/
@[spec_gen] theorem bne_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      ((addr ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset) ((addr ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (addr + 4)                   ((addr ↦ᵢ .BNE rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec rs1 rs2 offset v1 v2 addr

/-- BEQ spec for any code memory:
    Branch taken (v1 = v2) → PC = addr + sext(offset)
    Branch not taken (v1 ≠ v2) → PC = addr + 4 -/
@[spec_gen] theorem beq_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      ((addr ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset) ((addr ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (addr + 4)                   ((addr ↦ᵢ .BEQ rs1 rs2 offset) ** (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec rs1 rs2 offset v1 v2 addr

/-- JAL x0 spec for any code memory: pure PC jump, no register/memory changes.
    Since x0 writes are dropped, JAL x0 just updates PC. -/
@[spec_gen] theorem jal_x0_spec_gen (offset : BitVec 21) (addr : Addr) :
    cpsTriple addr (addr + signExtend21 offset)
      (addr ↦ᵢ .JAL .x0 offset)
      (addr ↦ᵢ .JAL .x0 offset) :=
  generic_nop_spec (.JAL .x0 offset) addr (addr + signExtend21 offset)
    (by intro s hpc; simp [execInstrBr, MachineState.setReg, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

end EvmAsm
