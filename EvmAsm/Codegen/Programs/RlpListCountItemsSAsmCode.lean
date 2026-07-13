import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase

namespace EvmAsm.Codegen.RlpListCountItemsSAsm

open EvmAsm.Rv64 EvmAsm.Rv64.RLP
open EvmAsm.Rv64.SAsm

/-! ## Embedded verified-code ties and local-call adapters -/

theorem wrapper_length : rlpListCountItemsWrapper_prog.length = 30 := by decide

theorem total_length : rlpListCountItems_prog.length = 186 := by
  simp only [rlpListCountItems_prog, List.length_append, wrapper_length,
    rlp_walk_init_prog_length, rlp_walk_next_prog_length]

theorem embedded_walk_init :
    (rlpListCountItems_prog.drop rlpListCountItemsWrapper_prog.length).take
      rlp_walk_init_prog.length = rlp_walk_init_prog := by decide

theorem embedded_walk_next :
    rlpListCountItems_prog.drop
      (rlpListCountItemsWrapper_prog.length + rlp_walk_init_prog.length) =
      rlp_walk_next_prog := by decide

theorem reemit_byte_tie :
    rlpListCountItems_prog =
      (show List Instr from rlpListCountItemsWrapper_prog) ++
        (show List Instr from rlp_walk_init_prog) ++ rlp_walk_next_prog := by rfl

abbrev B : Word := (GuestAddrs.rlp_list_count_items : Word)
abbrev WI : Word := B + 120
abbrev WN : Word := B + 332

def code : CodeReq := CodeReq.ofProg B rlpListCountItems_prog

theorem walkInit_sub : ∀ a i, rlp_walk_init_code WI a = some i → code a = some i := by
  intro a i h_mem
  exact CodeReq.ofProg_mono_sub B WI rlpListCountItems_prog rlp_walk_init_prog
    30 (by simp [WI]) (by simpa [wrapper_length] using embedded_walk_init)
    (by rw [total_length, rlp_walk_init_prog_length]; omega)
    (by rw [total_length]; norm_num) a i h_mem

theorem walkNext_sub : ∀ a i, rlp_walk_next_code WN a = some i → code a = some i := by
  intro a i h_mem
  exact CodeReq.ofProg_mono_sub B WN rlpListCountItems_prog rlp_walk_next_prog
    83 (by simp [WN]) (by simpa [wrapper_length, rlp_walk_init_prog_length]
      using embedded_walk_next)
    (by rw [total_length, rlp_walk_next_prog_length])
    (by rw [total_length]; norm_num) a i h_mem

/-- Lift the wrapper's local strict-list initialization call. -/
theorem callWalkInit {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (h_pre : Prest.pcFree)
    (h_callee : cpsTripleWithin n WI ((B + 36) &&& ~~~(1 : Word))
      (rlp_walk_init_code WI) ((.x1 ↦ᵣ (B + 36)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 32) (B + 36) code
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h_call := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 32) (calleeEntry := WI) (vOld := oldRa)
    (calleeCode := rlp_walk_init_code WI) (Prest := Prest) (Q := Q)
    (88 : BitVec 21) (by decide) (by decide) h_pre
    (CodeReq.Disjoint.singleton_ofProg (by decide)) h_callee
  exact cpsTripleWithin_extend_code (CodeReq.union_split_mono
    (fun a i h_code => CodeReq.ofProg_mono_sub B (B + 32)
      rlpListCountItems_prog [.JAL .x1 (88 : BitVec 21)] 8 (by bv_omega)
      (by rfl) (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)
      a i h_code) walkInit_sub) h_call

/-- Lift the wrapper's local strict-item call. -/
theorem callWalkNext {n : Nat} {Prest Q : Assertion} (oldRa : Word)
    (h_pre : Prest.pcFree)
    (h_callee : cpsTripleWithin n WN ((B + 60) &&& ~~~(1 : Word))
      (rlp_walk_next_code WN) ((.x1 ↦ᵣ (B + 60)) ** Prest) Q) :
    cpsTripleWithin (1 + n) (B + 56) (B + 60) code
      ((.x1 ↦ᵣ oldRa) ** Prest) Q := by
  have h_call := WP.cpsCallWithin
    (nSteps := n) (callerPC := B + 56) (calleeEntry := WN) (vOld := oldRa)
    (calleeCode := rlp_walk_next_code WN) (Prest := Prest) (Q := Q)
    (276 : BitVec 21) (by decide) (by decide) h_pre
    (CodeReq.Disjoint.singleton_ofProg (by decide)) h_callee
  exact cpsTripleWithin_extend_code (CodeReq.union_split_mono
    (fun a i h_code => CodeReq.ofProg_mono_sub B (B + 56)
      rlpListCountItems_prog [.JAL .x1 (276 : BitVec 21)] 14 (by bv_omega)
      (by rfl) (by rw [total_length]; norm_num) (by rw [total_length]; norm_num)
      a i h_code) walkNext_sub) h_call

#print axioms reemit_byte_tie
#print axioms callWalkInit
#print axioms callWalkNext

end EvmAsm.Codegen.RlpListCountItemsSAsm
