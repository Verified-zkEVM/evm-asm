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
      (CodeReq.singleton addr (.LW rd rs1 offset))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) :=
  generic_lw_spec rd rs1 v_addr v_old mem_val offset addr hrd_ne_x0 hvalid

/-- SLTIU spec for any code memory (rd == rs1 case):
    rd := (v <u sext(imm)) ? 1 : 0 -/
@[spec_gen] theorem sltiu_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SLTIU rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word))) :=
  generic_1reg_spec (.SLTIU rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- XORI spec for any code memory (rd == rs1 case):
    rd := v ^^^ sext(imm) -/
@[spec_gen] theorem xori_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.XORI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v ^^^ signExtend12 imm)) :=
  generic_1reg_spec (.XORI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SRL spec for any code memory (rd = rs1 case):
    rd := rd >>> (rs2.toNat % 32) -/
@[spec_gen] theorem srl_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SRL rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 >>> (v2.toNat % 32))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SRL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLL spec for any code memory (rd = rs1 case):
    rd := rd <<< (rs2.toNat % 32) -/
@[spec_gen] theorem sll_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SLL rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 <<< (v2.toNat % 32))) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SLL rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADD spec for any code memory (rd = rs1 case):
    rd := rd + rs2 -/
@[spec_gen] theorem add_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.ADD rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.ADD rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB spec for any code memory (rd = rs1 case):
    rd := rd - rs2 -/
@[spec_gen] theorem sub_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SUB rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SUB rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- AND spec for any code memory (rd = rs1 case):
    rd := rd &&& rs2 -/
@[spec_gen] theorem and_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.AND rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 &&& v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.AND rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- OR spec for any code memory (rd = rs1 case):
    rd := rd ||| rs2 -/
@[spec_gen] theorem or_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.OR rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ||| v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.OR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- XOR spec for any code memory (rd = rs1 case):
    rd := rd ^^^ rs2 -/
@[spec_gen] theorem xor_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.XOR rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ^^^ v2)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.XOR rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLTU spec for any code memory (rd = rs1 case):
    rd := if rd <u rs2 then 1 else 0 -/
@[spec_gen] theorem sltu_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SLTU rd rd rs2))
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0)) ** (rs2 ↦ᵣ v2)) :=
  generic_2reg_rd_eq_rs1_spec (.SLTU rd rd rs2) rd rs2 v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrd hrs2; simp [execInstrBr, hrd, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDI spec for any code memory (rd = rs1 case):
    rd := rd + signExtend12(imm) -/
@[spec_gen] theorem addi_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.ADDI rd rd imm))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v + signExtend12 imm)) :=
  generic_1reg_spec (.ADDI rd rd imm) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- LI spec for any code memory (not just a single-instruction loadProgram). -/
@[spec_gen] theorem li_spec_gen (rd : Reg) (v_old imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.LI rd imm))
      (rd ↦ᵣ v_old)
      (rd ↦ᵣ imm) :=
  generic_1reg_spec (.LI rd imm) rd v_old _ addr hrd_ne_x0
    (by intro s _ _; simp [execInstrBr])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- LI spec for any code memory with regOwn (no v_old needed). -/
@[spec_gen] theorem li_spec_gen_own (rd : Reg) (imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.LI rd imm))
      (regOwn rd)
      (rd ↦ᵣ imm) := by
  exact cpsTriple_of_forall_regIs_to_regOwn_single (CodeReq.singleton addr (.LI rd imm))
    (fun v_old => li_spec_gen rd v_old imm addr hrd_ne_x0)

/-- ECALL halt spec: when x5 = 0, ECALL halts. -/
@[spec_gen] theorem ecall_halt_spec_gen (exitCode : Word) (addr : Addr) :
    cpsHaltTriple addr
      (CodeReq.singleton addr .ECALL)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR s hcr hPR hpc; subst hpc
  -- Extract code fetch from CodeReq
  have hfetch : s.code s.pc = some .ECALL :=
    (CodeReq.singleton_satisfiedBy s.pc .ECALL s).mp hcr
  have hx5 : s.getReg .x5 = (0 : Word) :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  -- Witness: 0 steps, the current state s is already halted
  refine ⟨0, s, rfl, ?_, hPR⟩
  -- Show isHalted s = true
  simp only [isHalted, step_ecall_halt s hfetch hx5, Option.isNone]

/-- SW rs1 rs2 offset: mem[rs1 + sext(offset)] := rs2 (generalized for any CodeMem) -/
@[spec_gen] theorem sw_spec_gen (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) :=
  generic_sw_spec rs1 rs2 v_addr v_data mem_old offset addr hvalid

/-- SW spec with memOwn (no mem_old needed). -/
@[spec_gen] theorem sw_spec_gen_own (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hcr hPR hpc
  obtain ⟨h, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hR1, hRest, hd2, hu2, hpR1, hpRest⟩ := hpP
  obtain ⟨hR2, hM, hd3, hu3, hpR2, hpM⟩ := hpRest
  obtain ⟨v, hv⟩ := hpM
  exact sw_spec_gen rs1 rs2 v_addr v_data v offset addr hvalid R hR s hcr
    ⟨h, hcompat, h_P, h_R, hdisj, hunion,
     ⟨hR1, hRest, hd2, hu2, hpR1, ⟨hR2, hM, hd3, hu3, hpR2, hv⟩⟩, hpR⟩ hpc

/-- SW rs1 x0 offset: mem[rs1 + sext(offset)] := 0.
    Specialized version of sw_spec_gen for x0 (always reads as 0).
    Does not require (x0 ↦ᵣ 0) in pre/post. -/
@[spec_gen] theorem sw_x0_spec_gen (rs1 : Reg) (v_addr mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SW rs1 .x0 offset))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) :=
  generic_sw_x0_spec rs1 v_addr mem_old offset addr hvalid

-- ============================================================================
-- Section 4: Frame Embedding for cpsTriple
-- ============================================================================

/-- Frame on the right: if cpsTriple cr P → Q, then cpsTriple cr (P ** F) → (Q ** F). -/
theorem cpsTriple_frame_left (entry exit_ : Addr) (cr : CodeReq)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr (P ** F) (Q ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

/-- Frame for cpsBranch: if cpsBranch cr P → Q_t | Q_f, then cpsBranch cr (P ** F) → (Q_t ** F) | (Q_f ** F). -/
theorem cpsBranch_frame_left (entry : Addr) (cr : CodeReq)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch entry cr (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hcase⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, hcase.elim
    (fun ⟨hpc', hpost⟩ => Or.inl ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)
    (fun ⟨hpc', hpost⟩ => Or.inr ⟨hpc', holdsFor_sepConj_assoc.mpr hpost⟩)⟩

/-- Frame for cpsNBranch: if cpsNBranch cr P → exits, then cpsNBranch cr (P ** F) → exits with F. -/
theorem cpsNBranch_frame_left (entry : Addr) (cr : CodeReq)
    (P : Assertion) (exits : List (Addr × Assertion))
    (F : Assertion) (hF : F.pcFree)
    (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr (P ** F) (exits.map fun (a, Q) => (a, Q ** F)) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, ⟨exit_, hmem, hpc', hpost⟩⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, ⟨(exit_.1, exit_.2 ** F),
    List.mem_map.mpr ⟨exit_, hmem, rfl⟩,
    hpc', holdsFor_sepConj_assoc.mpr hpost⟩⟩

/-- Frame for cpsNBranch on the right: if cpsNBranch cr P → exits, then cpsNBranch cr (F ** P) → exits with F. -/
theorem cpsNBranch_frame_right (entry : Addr) (cr : CodeReq)
    (P : Assertion) (exits : List (Addr × Assertion))
    (F : Assertion) (hF : F.pcFree)
    (h : cpsNBranch entry cr P exits) :
    cpsNBranch entry cr (F ** P) (exits.map fun (a, Q) => (a, F ** Q)) := by
  intro R hR s hcr hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, ⟨exit_, hmem, hpc', hpost⟩⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR hpc
  exact ⟨k, s', hstep, ⟨(exit_.1, F ** exit_.2),
    List.mem_map.mpr ⟨exit_, hmem, rfl⟩,
    hpc', holdsFor_sepConj_pull_second.mpr hpost⟩⟩

/-- Frame on the left: if cpsTriple cr P → Q, then cpsTriple cr (F ** P) → (F ** Q). -/
theorem cpsTriple_frame_right (entry exit_ : Addr) (cr : CodeReq)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ cr P Q) :
    cpsTriple entry exit_ cr (F ** P) (F ** Q) := by
  intro R hR s hcr hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hpc', hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (entry : Addr) (cr : CodeReq)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry cr P Q) :
    cpsHaltTriple entry cr (P ** F) (Q ** F) := by
  intro R hR s hcr hPFR hpc
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hhalt, hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR' hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hpost⟩

/-- Frame on the left for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_right (entry : Addr) (cr : CodeReq)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry cr P Q) :
    cpsHaltTriple entry cr (F ** P) (F ** Q) := by
  intro R hR s hcr hFPR hpc
  have hPFR := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hhalt, hpost⟩ := h (F ** R) (pcFree_sepConj hF hR) s hcr hPFR hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_pull_second.mpr hpost⟩

-- ============================================================================
-- Section 4b: CodeReq extension helpers for multi-instruction specs
-- ============================================================================

/-- Extend a cpsHaltTriple to require more code. -/
private theorem cpsHaltTriple_extend_code {entry : Addr} {cr cr' : CodeReq} {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsHaltTriple entry cr P Q) :
    cpsHaltTriple entry cr' P Q := by
  intro R hR s hcr' hPR hpc
  exact h R hR s (CodeReq.SatisfiedBy_mono s hmono hcr') hPR hpc

/-- Monotonicity lemma: left singleton ≤ union. -/
private theorem cr_le_union_left (cr1 cr2 : CodeReq) :
    ∀ a i, cr1 a = some i → (cr1.union cr2) a = some i := by
  intro a i h
  simp only [CodeReq.union, h]

/-- Monotonicity lemma: right component ≤ union when cr1 has no entry at that address. -/
private theorem cr_le_union_right_of_none (cr1 cr2 : CodeReq) (a : Addr) (i : Instr)
    (hnone : cr1 a = none) (h : cr2 a = some i) : (cr1.union cr2) a = some i := by
  simp only [CodeReq.union, hnone, h]

/-- A singleton CodeReq has none at any address other than the singleton's address. -/
private theorem singleton_none_of_ne (a a' : Addr) (i : Instr) (h : a ≠ a') :
    CodeReq.singleton a i a' = none := by
  simp only [CodeReq.singleton]
  simp [show (a' == a) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]

/-- A singleton lookup at some address is `some i` only if the address matches. -/
private theorem singleton_addr_of_some (a a' : Addr) (i i' : Instr)
    (h : CodeReq.singleton a i a' = some i') : a' = a := by
  simp only [CodeReq.singleton] at h
  by_cases heq : a' == a
  · exact beq_iff_eq.mp heq
  · simp [heq] at h

-- ============================================================================
-- Section 5: Generalized HALT spec (for arbitrary CodeMem)
-- ============================================================================

/-- HALT exitCode on arbitrary CodeMem.
    Uses regOwn (no old values needed).
    The CodeReq requires the 3 instructions: LI x5 0, LI x10 exitCode, ECALL. -/
theorem halt_spec_gen (exitCode : Word) (base : Addr) :
    cpsHaltTriple base
      (CodeReq.union (CodeReq.singleton base (.LI .x5 0))
        (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 exitCode))
          (CodeReq.singleton (base + 8) .ECALL)))
      (regOwn .x5 ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  have s1 := li_spec_gen_own .x5 (0 : Word) base (by nofun)
  have s2 := li_spec_gen_own .x10 exitCode (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2
  have s1f := cpsTriple_frame_left _ _ _ _ _ (regOwn .x10) (pcFree_regOwn .x10) s1
  have s2f := cpsTriple_frame_right _ _ _ _ _ (.x5 ↦ᵣ (0 : Word)) (pcFree_regIs .x5 0) s2
  have s1e : cpsTriple _ _ (CodeReq.union (CodeReq.singleton base (.LI .x5 0))
    (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 exitCode))
      (CodeReq.singleton (base + 8) .ECALL))) _ _ :=
    cpsTriple_extend_code (CodeReq.union_mono_left _ _) s1f
  have s2e : cpsTriple _ _ (CodeReq.union (CodeReq.singleton base (.LI .x5 0))
    (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 exitCode))
      (CodeReq.singleton (base + 8) .ECALL))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.union_mono_left _ _)) s2f
  have s12 := cpsTriple_seq _ _ _ _ _ _ _ s1e s2e
  have s3 := ecall_halt_spec_gen exitCode (base + 8)
  have s3e : cpsHaltTriple _ (CodeReq.union (CodeReq.singleton base (.LI .x5 0))
    (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 exitCode))
      (CodeReq.singleton (base + 8) .ECALL))) _ _ :=
    cpsHaltTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (fun _ _ h => h))) s3
  exact cpsTriple_seq_halt _ _ _ _ _ _ s12 s3e

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
      (CodeReq.union (CodeReq.singleton addr (.LI .x6 val))
        (CodeReq.singleton (addr + 4) (.SW .x7 .x6 offset)))
      ((.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  have s1 := li_spec_gen .x6 x6_old val addr (by nofun)
  have s2 := sw_spec_gen .x7 .x6 x7_val val mem_old offset (addr + 4) hvalid
  rw [show (addr + 4 : Addr) + 4 = addr + 8 from by bv_omega] at s2
  have s1f := cpsTriple_frame_left _ _ _ _ _
    ((.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
    (pcFree_sepConj (pcFree_regIs .x7 x7_val) (pcFree_memIs _ mem_old)) s1
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTriple_seq_ext_with_perm _ _ _ _ _ _
      (CodeReq.union_mono_left _ _)
      (CodeReq.mono_union_right
        (CodeReq.Disjoint.singleton (by bv_omega) _ _) (fun _ _ h => h))
      _ _ _ _
      (fun h hp => by xperm_hyp hp) s1f s2)

/-- Combined LI+SW spec with regOwn and memOwn (no x6_old or mem_old needed). -/
theorem storeWord_spec_gen_own (val : Word) (offset : BitVec 12)
    (x7_val : Word) (addr : Addr)
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple addr (addr + 8)
      (CodeReq.union (CodeReq.singleton addr (.LI .x6 val))
        (CodeReq.singleton (addr + 4) (.SW .x7 .x6 offset)))
      (regOwn .x6 ** (.x7 ↦ᵣ x7_val) ** memOwn (x7_val + signExtend12 offset))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, h_P, h_R, hdisj, hunion, hpP, hpR⟩ := hPR
  obtain ⟨hOwn, hRest, hd2, hu2, hpOwn, hpRest⟩ := hpP
  obtain ⟨v_old, hv_old⟩ := hpOwn
  obtain ⟨hR7, hMem, hd3, hu3, hpR7, hpMem⟩ := hpRest
  obtain ⟨m_old, hm_old⟩ := hpMem
  exact storeWord_spec_gen val offset v_old x7_val m_old addr hvalid R hR s hcr
    ⟨hp, hcompat, h_P, h_R, hdisj, hunion,
     ⟨hOwn, hRest, hd2, hu2, hv_old, ⟨hR7, hMem, hd3, hu3, hpR7, hm_old⟩⟩, hpR⟩ hpc

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
      (CodeReq.singleton addr .ECALL)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs (inputBytes.drop nbytes.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat))) := by
  intro R hR s hcr hPR hpc; subst hpc
  -- Extract code fetch and register values from precondition
  have hfetch : s.code s.pc = some .ECALL :=
    (CodeReq.singleton_satisfiedBy s.pc .ECALL s).mp hcr
  have hx5 : s.getReg .x5 = 0xF1#32 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx10 : s.getReg .x10 = bufAddr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hx11 : s.getReg .x11 = nbytes :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))
  have hpi : s.privateInput = inputBytes :=
    (holdsFor_privateInputIs _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))))
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

    -- Step A: Pull privateInputIs (4th element) to front, apply drop
    have h1 := holdsFor_pullFourth (A := (.x5 ↦ᵣ 0xF1#32))
      (B := (.x10 ↦ᵣ bufAddr)) (C := (.x11 ↦ᵣ nbytes))
      (D := privateInputIs inputBytes) (E := memBufferIs bufAddr oldWords) hPR
    -- h1 : ((privateInputIs inputBytes ** x5 ** x10 ** x11 ** memBuf) ** R).holdsFor s

    -- Apply privateInput drop
    -- First, use holdsFor_sepConj_assoc to get (pI ** rest) form for the drop lemma
    have h1' := holdsFor_sepConj_assoc.mp h1
    -- h1' : (privateInputIs inputBytes ** ((x5 ** x10 ** x11 ** memBuf) ** R)).holdsFor s
    have h2' := @holdsFor_sepConj_privateInputIs_drop inputBytes nbytes.toNat _ s h1'
    -- h2' : (privateInputIs (inputBytes.drop nbytes.toNat) ** rest).holdsFor {s with pi.drop n}
    -- Reassociate back
    have h3 := holdsFor_sepConj_assoc.mpr h2'
    -- h3 : ((privateInputIs dropped ** (x5 ** x10 ** x11 ** memBuf)) ** R).holdsFor s_drop

    -- Step B: Push privateInputIs back to position, pull memBuf to front
    -- h3 has shape ((pI' ** (x5 ** x10 ** x11 ** memBuf)) ** R)
    -- We need to get memBuf to front.
    -- First push pI' into the chain:
    have h4 := holdsFor_pushFourth
      (A := (.x5 ↦ᵣ 0xF1#32))
      (B := (.x10 ↦ᵣ bufAddr))
      (C := (.x11 ↦ᵣ nbytes))
      (D := privateInputIs (inputBytes.drop nbytes.toNat))
      (E := memBufferIs bufAddr oldWords) h3
    -- h4 : ((x5 ** x10 ** x11 ** pI' ** memBuf) ** R).holdsFor s_drop

    -- Pull memBuf to front using pull_second repeatedly
    have hp1 := holdsFor_sepConj_pull_second.mp h4
    have hp2 := holdsFor_sepConj_pull_second.mp hp1
    have hp3 := holdsFor_sepConj_pull_second.mp hp2
    have hp4 := holdsFor_sepConj_pull_second.mp hp3
    -- hp4 : (memBuf ** (pI' ** x11 ** x10 ** x5 ** R)).holdsFor s_drop

    -- Apply writeBytesAsWords lemma
    -- s_write = s_drop.writeBytesAsWords (s.getReg .x10) (s.privateInput.take (s.getReg .x11).toNat)
    -- = s_drop.writeBytesAsWords bufAddr (inputBytes.take nbytes.toNat) [by hx10, hpi, hx11]
    have hbytes_eq : s.privateInput.take (s.getReg .x11).toNat = inputBytes.take nbytes.toNat := by
      rw [hpi, hx11]
    have hbytes_len : (inputBytes.take nbytes.toNat).length = 4 * oldWords.length := by
      rw [List.length_take, Nat.min_eq_left hLen, hNbytes]

    have h5 : ((memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat)) **
      (privateInputIs (inputBytes.drop nbytes.toNat) ** (.x11 ↦ᵣ nbytes) ** (.x10 ↦ᵣ bufAddr) **
       (.x5 ↦ᵣ 0xF1#32) ** R))).holdsFor
      ({ s with privateInput := s.privateInput.drop (s.getReg .x11).toNat }.writeBytesAsWords
        (s.getReg .x10) (s.privateInput.take (s.getReg .x11).toNat)) := by
      rw [hx10, hbytes_eq]
      have : { s with privateInput := s.privateInput.drop (s.getReg .x11).toNat } =
             { s with privateInput := s.privateInput.drop nbytes.toNat } := by
        rw [hx11]
      rw [this]
      exact holdsFor_sepConj_memBufferIs_writeBytesAsWords hbytes_len hp4

    -- Push memBuf back
    have hq4 := holdsFor_sepConj_pull_second.mpr h5
    have hq3 := holdsFor_sepConj_pull_second.mpr hq4
    have hq2 := holdsFor_sepConj_pull_second.mpr hq3
    have hq1 := holdsFor_sepConj_pull_second.mpr hq2
    -- hq1 : ((x5 ** x10 ** x11 ** pI' ** memBuf') ** R).holdsFor s_write

    -- Step C: Apply setPC
    have hpcfree : ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs (inputBytes.drop nbytes.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat))).pcFree :=
      pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
        (pcFree_sepConj (pcFree_regIs _ _)
          (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _))))
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
      (CodeReq.union (CodeReq.singleton base (.LI .x5 0xF1#32))
        (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 bufAddr))
          (CodeReq.union (CodeReq.singleton (base + 8) (.LI .x11 nbytes_val))
            (CodeReq.singleton (base + 12) .ECALL))))
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 **
       privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes_val) **
       privateInputIs (inputBytes.drop nbytes_val.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes_val.toNat))) := by
  have s1 := li_spec_gen_own .x5 (0xF1#32) base (by nofun)
  have s1f := cpsTriple_frame_left _ _ _ _ _
    (regOwn .x10 ** regOwn .x11 ** privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
    (pcFree_sepConj (pcFree_regOwn .x10) (pcFree_sepConj (pcFree_regOwn .x11)
      (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))) s1
  have s2 := li_spec_gen_own .x10 bufAddr (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2
  have s2f := cpsTriple_frame_right _ _ _ _ _
    ((.x5 ↦ᵣ 0xF1#32) ** regOwn .x11 ** privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regOwn .x11)
      (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))) s2
  have s1e : cpsTriple _ _
    (CodeReq.union (CodeReq.singleton base (.LI .x5 0xF1#32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 bufAddr))
        (CodeReq.union (CodeReq.singleton (base + 8) (.LI .x11 nbytes_val))
          (CodeReq.singleton (base + 12) .ECALL)))) _ _ :=
    cpsTriple_extend_code (CodeReq.union_mono_left _ _) s1f
  have s2e : cpsTriple _ _
    (CodeReq.union (CodeReq.singleton base (.LI .x5 0xF1#32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 bufAddr))
        (CodeReq.union (CodeReq.singleton (base + 8) (.LI .x11 nbytes_val))
          (CodeReq.singleton (base + 12) .ECALL)))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.union_mono_left _ _)) s2f
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1e s2e
  have s3 := li_spec_gen_own .x11 nbytes_val (base + 8) (by nofun)
  rw [show (base + 8 : Addr) + 4 = base + 12 from by bv_omega] at s3
  have s3f := cpsTriple_frame_right _ _ _ _ _
    ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))) s3
  have s3e : cpsTriple _ _
    (CodeReq.union (CodeReq.singleton base (.LI .x5 0xF1#32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 bufAddr))
        (CodeReq.union (CodeReq.singleton (base + 8) (.LI .x11 nbytes_val))
          (CodeReq.singleton (base + 12) .ECALL)))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.union_mono_left _ _))) s3f
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3e
  have s4 := ecall_hint_read_spec_gen bufAddr nbytes_val inputBytes oldWords (base + 12) hLen hNbytes
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega] at s4
  have s4e : cpsTriple _ _
    (CodeReq.union (CodeReq.singleton base (.LI .x5 0xF1#32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.LI .x10 bufAddr))
        (CodeReq.union (CodeReq.singleton (base + 8) (.LI .x11 nbytes_val))
          (CodeReq.singleton (base + 12) .ECALL)))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
            (fun _ _ h => h)))) s4
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s123 s4e)

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
      (CodeReq.singleton addr .ECALL)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  intro R hR s hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL :=
    (CodeReq.singleton_satisfiedBy s.pc .ECALL s).mp hcr
  have hx5 : s.getReg .x5 = BitVec.ofNat 32 0x02 :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hx10 : s.getReg .x10 = (13 : Word) :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hx11 : s.getReg .x11 = bufPtr :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))))
  have hx12 : s.getReg .x12 = nbytes :=
    (holdsFor_regIs _ _ s).mp (holdsFor_sepConj_elim_left
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))))
  have hmemBuf : (memBufferIs bufPtr words).holdsFor s :=
    holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))))
  have hgetmem : ∀ (k : Nat) (hk : k < words.length),
      s.getMem (bufPtr + BitVec.ofNat 32 (4 * k)) = words[k]'hk :=
    fun k hk => getMem_of_holdsFor_memBufferIs hmemBuf k hk
  have hreadFull : s.readBytes bufPtr (4 * words.length) =
      words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3]) :=
    readBytes_of_words hgetmem hAligned
  have hread : s.readBytes (s.getReg .x11) (s.getReg .x12).toNat =
      (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat := by
    rw [hx11, hx12, ← readBytes_take s bufPtr nbytes.toNat (4 * words.length) hLen, hreadFull]
  let expBytes := (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat
  refine ⟨1, (s.appendPublicValues expBytes).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (step s).bind (stepN 0) = some _
    rw [step_ecall_write_public s hfetch hx5 hx10]
    simp only [Option.bind, stepN]
    congr 1; congr 1
    exact congrArg (fun b => s.appendPublicValues b) hread
  · have h1 := holdsFor_pullFifth (A := (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)))
      (B := (.x10 ↦ᵣ (13 : Word))) (C := (.x11 ↦ᵣ bufPtr))
      (D := (.x12 ↦ᵣ nbytes))
      (E := publicValuesIs oldPV) (F := memBufferIs bufPtr words) hPR
    have h1' := holdsFor_sepConj_assoc.mp h1
    have h2' := @holdsFor_sepConj_publicValuesIs_appendPublicValues oldPV
      expBytes _ s h1'
    have h3 := holdsFor_sepConj_assoc.mpr h2'
    have h4 := holdsFor_pushFifth
      (A := (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)))
      (B := (.x10 ↦ᵣ (13 : Word)))
      (C := (.x11 ↦ᵣ bufPtr))
      (D := (.x12 ↦ᵣ nbytes))
      (E := publicValuesIs (oldPV ++ expBytes))
      (F := memBufferIs bufPtr words) h3
    have hpcfree : ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ expBytes) ** memBufferIs bufPtr words).pcFree :=
      pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
          (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)))))
    exact holdsFor_pcFree_setPC (pcFree_sepConj hpcfree hR) _ _ h4

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
      (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
      (CodeReq.singleton (base + 4) (.LI .x10 13) |>.union
      (CodeReq.singleton (base + 8) (.LI .x11 bufPtr) |>.union
      (CodeReq.singleton (base + 12) (.LI .x12 nbytes) |>.union
       (CodeReq.singleton (base + 16) .ECALL)))))
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  -- Step 1: LI x5 0x02
  have s1 := li_spec_gen_own .x5 (BitVec.ofNat 32 0x02) base (by nofun)
  have s1f := cpsTriple_frame_left _ _ _ _ _
    (regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** publicValuesIs oldPV ** memBufferIs bufPtr words)
    (pcFree_sepConj (pcFree_regOwn .x10) (pcFree_sepConj (pcFree_regOwn .x11)
      (pcFree_sepConj (pcFree_regOwn .x12)
        (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))) s1
  -- Step 2: LI x10 13
  have s2 := li_spec_gen_own .x10 (13 : Word) (base + 4) (by nofun)
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_omega] at s2
  have s2f := cpsTriple_frame_right _ _ _ _ _
    ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** regOwn .x11 ** regOwn .x12 **
     publicValuesIs oldPV ** memBufferIs bufPtr words)
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regOwn .x11)
      (pcFree_sepConj (pcFree_regOwn .x12)
        (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))) s2
  -- Extend to full CR
  have s1e : cpsTriple _ _
    (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
    (CodeReq.singleton (base + 4) (.LI .x10 13) |>.union
    (CodeReq.singleton (base + 8) (.LI .x11 bufPtr) |>.union
    (CodeReq.singleton (base + 12) (.LI .x12 nbytes) |>.union
     (CodeReq.singleton (base + 16) .ECALL))))) _ _ :=
    cpsTriple_extend_code (CodeReq.union_mono_left _ _) s1f
  have s2e : cpsTriple _ _
    (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
    (CodeReq.singleton (base + 4) (.LI .x10 13) |>.union
    (CodeReq.singleton (base + 8) (.LI .x11 bufPtr) |>.union
    (CodeReq.singleton (base + 12) (.LI .x12 nbytes) |>.union
     (CodeReq.singleton (base + 16) .ECALL))))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.union_mono_left _ _)) s2f
  have s12 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s1e s2e
  -- Step 3: LI x11 bufPtr
  have s3 := li_spec_gen_own .x11 bufPtr (base + 8) (by nofun)
  rw [show (base + 8 : Addr) + 4 = base + 12 from by bv_omega] at s3
  have s3f := cpsTriple_frame_right _ _ _ _ _
    ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
     regOwn .x12 ** publicValuesIs oldPV ** memBufferIs bufPtr words)
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_regOwn .x12)
        (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))) s3
  have s3e : cpsTriple _ _
    (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
    (CodeReq.singleton (base + 4) (.LI .x10 13) |>.union
    (CodeReq.singleton (base + 8) (.LI .x11 bufPtr) |>.union
    (CodeReq.singleton (base + 12) (.LI .x12 nbytes) |>.union
     (CodeReq.singleton (base + 16) .ECALL))))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.union_mono_left _ _))) s3f
  have s123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s12 s3e
  -- Step 4: LI x12 nbytes
  have s4 := li_spec_gen_own .x12 nbytes (base + 12) (by nofun)
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_omega] at s4
  have s4f := cpsTriple_frame_right _ _ _ _ _
    ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) **
     publicValuesIs oldPV ** memBufferIs bufPtr words)
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_regIs _ _)
        (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))) s4
  have s4e : cpsTriple _ _
    (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
    (CodeReq.singleton (base + 4) (.LI .x10 13) |>.union
    (CodeReq.singleton (base + 8) (.LI .x11 bufPtr) |>.union
    (CodeReq.singleton (base + 12) (.LI .x12 nbytes) |>.union
     (CodeReq.singleton (base + 16) .ECALL))))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
            (CodeReq.union_mono_left _ _)))) s4f
  have s1234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) s123 s4e
  -- Step 5: ECALL WRITE
  have s5 := ecall_write_public_spec_gen bufPtr nbytes oldPV words (base + 16) hLen hAligned
  rw [show (base + 16 : Addr) + 4 = base + 20 from by bv_omega] at s5
  have s5e : cpsTriple _ _
    (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
    (CodeReq.singleton (base + 4) (.LI .x10 13) |>.union
    (CodeReq.singleton (base + 8) (.LI .x11 bufPtr) |>.union
    (CodeReq.singleton (base + 12) (.LI .x12 nbytes) |>.union
     (CodeReq.singleton (base + 16) .ECALL))))) _ _ :=
    cpsTriple_extend_code
      (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
        (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
          (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
            (CodeReq.mono_union_right (CodeReq.Disjoint.singleton (by bv_omega) _ _)
              (fun _ _ h => h))))) s5
  exact cpsTriple_consequence _ _ _ _ _ _ _
    (fun _ hp => hp)
    (fun h hp => by xperm_hyp hp)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) s1234 s5e)

/-- SLTU spec for 3 distinct registers:
    rd := (rs1 < rs2) ? 1 : 0, preserving rs1 and rs2 -/
@[spec_gen] theorem sltu_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SLTU rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then 1 else 0))) :=
  generic_3reg_spec (.SLTU rd rs1 rs2) rs1 rs2 rd v1 v2 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 hrs2; simp [execInstrBr, hrs1, hrs2])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- OR spec for 3 distinct registers:
    rd := rs1 ||| rs2, preserving rs1 and rs2 -/
@[spec_gen] theorem or_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.OR rd rs1 rs2))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 ||| v2))) :=
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
      (CodeReq.singleton addr (.ANDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 &&& signExtend12 imm))) :=
  generic_2reg_spec (.ANDI rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SRLI spec for any code memory (rd == rs1 case):
    rd := rd >>> shamt -/
@[spec_gen] theorem srli_spec_gen_same (rd : Reg) (v : Word) (shamt : BitVec 5)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SRLI rd rd shamt))
      (rd ↦ᵣ v)
      (rd ↦ᵣ (v >>> shamt.toNat)) :=
  generic_1reg_spec (.SRLI rd rd shamt) rd v _ addr hrd_ne_x0
    (by intro s _ hrd; simp [execInstrBr, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SLTIU spec for any code memory (rd ≠ rs1 case):
    rd := (rs1 <u sext(imm)) ? 1 : 0, preserving rs1 -/
@[spec_gen] theorem sltiu_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SLTIU rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.ult v1 (signExtend12 imm) then (1 : Word) else (0 : Word)))) :=
  generic_2reg_spec (.SLTIU rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- ADDI spec for any code memory (rd ≠ rs1 case):
    rd := rs1 + sext(imm), preserving rs1 -/
@[spec_gen] theorem addi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.ADDI rd rs1 imm))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) :=
  generic_2reg_spec (.ADDI rd rs1 imm) rs1 rd v1 v_old _ addr hrd_ne_x0
    (by intro s _ hrs1 _; simp [execInstrBr, hrs1])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- SUB spec for any code memory (rd = rs2 case):
    rd := rs1 - rd, preserving rs1 -/
@[spec_gen] theorem sub_spec_gen_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      (CodeReq.singleton addr (.SUB rd rs1 rd))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 - v2))) :=
  generic_2reg_spec (.SUB rd rs1 rd) rs1 rd v1 v2 _ addr hrd_ne_x0
    (by intro s _ hrs1 hrd; simp [execInstrBr, hrs1, hrd])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

/-- BNE spec for any code memory:
    Branch taken (v1 ≠ v2) → PC = addr + sext(offset)
    Branch not taken (v1 = v2) → PC = addr + 4 -/
@[spec_gen] theorem bne_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      (CodeReq.singleton addr (.BNE rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (addr + 4)                   ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) :=
  generic_bne_spec rs1 rs2 offset v1 v2 addr

/-- BEQ spec for any code memory:
    Branch taken (v1 = v2) → PC = addr + sext(offset)
    Branch not taken (v1 ≠ v2) → PC = addr + 4 -/
@[spec_gen] theorem beq_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      (CodeReq.singleton addr (.BEQ rs1 rs2 offset))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (addr + 4)                   ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) :=
  generic_beq_spec rs1 rs2 offset v1 v2 addr

/-- JAL x0 spec for any code memory: pure PC jump, no register/memory changes.
    Since x0 writes are dropped, JAL x0 just updates PC. -/
@[spec_gen] theorem jal_x0_spec_gen (offset : BitVec 21) (addr : Addr) :
    cpsTriple addr (addr + signExtend21 offset)
      (CodeReq.singleton addr (.JAL .x0 offset))
      empAssertion
      empAssertion :=
  generic_nop_spec (.JAL .x0 offset) addr (addr + signExtend21 offset)
    (by intro s hpc; simp [execInstrBr, MachineState.setReg, hpc])
    (by intro s hfetch; exact step_non_ecall_non_mem s _ hfetch (by nofun) (by nofun) (by rfl))

end EvmAsm
