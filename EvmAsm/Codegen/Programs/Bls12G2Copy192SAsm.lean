/-
  EvmAsm.Codegen.Programs.Bls12G2Copy192SAsm

  Byte-transparent ABI-frame caller port for `blsg2_copy192`:
  save `ra`, set `a2 = 24`, call verified `blsf_copy_quads`, restore `ra`, ret.
-/

import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Rv64.SAsm.Fn
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Codegen.Programs.Bls12G2
import EvmAsm.Codegen.Programs.Bls12FieldCopyQuadsSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm EvmAsm.Rv64.Tactics

namespace Bls12G2Copy192SAsm

#guard GuestAddrs.blsf_copy_quads = 0x8002f2bc
#guard GuestAddrs.blsg2_copy192 = 0x800339a0

/-- The caller's one-slot ABI frame: `ra` at 0(sp). -/
def copy192Frame : FrameDesc := [(.x1, 0)]

/-- Body after the prologue: set the quad count and call the generic copy helper. -/
def copy192Body : List Instr :=
  [ .LI .x12 (24 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_copy192 + 12)) ]

#guard abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) copy192Frame copy192Body
  = blsg2Copy192_prog

theorem copy192Prog_eq :
    abiFrameProg (-16 : BitVec 12) (16 : BitVec 12) copy192Frame copy192Body
      = blsg2Copy192_prog := rfl

/-- Non-adjacent caller/callee code requirement. -/
def copy192Cr : CodeReq :=
  (CodeReq.ofProg (0x800335b4 : Word) blsg2Copy192_prog).union
    (CodeReq.ofProg (0x8002eed0 : Word) blsfCopyQuads_prog)

private theorem callerSub :
    ∀ a i, CodeReq.ofProg (0x800335b4 : Word) blsg2Copy192_prog a = some i →
      copy192Cr a = some i := by
  intro a i h
  simp only [copy192Cr, CodeReq.union, h]

private theorem calleeSub :
    ∀ a i, CodeReq.ofProg (0x8002eed0 : Word) blsfCopyQuads_prog a = some i →
      copy192Cr a = some i := by
  intro a i h
  obtain ⟨k, hk, rfl⟩ := ofProg_some_range h
  have hnone : CodeReq.ofProg (0x800335b4 : Word) blsg2Copy192_prog
      ((0x8002eed0 : Word) + BitVec.ofNat 64 (4 * k)) = none := by
    apply CodeReq.ofProg_none_range
    intro k' hk' heq
    have hk7 : k' < 7 := hk'
    have hk8 : k < 8 := hk
    bv_omega
  simp only [copy192Cr, CodeReq.union, hnone, h]

private theorem add_sext0 (x : Word) : x + signExtend12 (0 : BitVec 12) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, show (signExtend12 (0 : BitVec 12)).toNat = 0 from by decide,
      Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

private theorem add_ofNat_zero (x : Word) : x + BitVec.ofNat 64 0 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt x.isLt]

private theorem addr_step8 (dst : Word) (p : Nat) :
    (dst + BitVec.ofNat 64 (8 * p)) + signExtend12 (8 : BitVec 12)
      = dst + BitVec.ofNat 64 (8 * (p + 1)) := by
  rw [show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from by decide,
      BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem cnt_step_down (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (-1 : BitVec 12) = BitVec.ofNat 64 n := by
  have e1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1 := by
    rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e1, show signExtend12 (-1 : BitVec 12) = (-1 : Word) from by decide,
      BitVec.add_assoc, show (1 : Word) + (-1 : Word) = 0 from by decide]
  exact BitVec.add_zero _

def lastLoaded (srcWords : List Word) (init : Word) (p : Nat) : Word :=
  if p = 0 then init else srcWords.getD (p - 1) 0

private theorem lastLoaded_succ (srcWords : List Word) (init : Word) (p : Nat) :
    lastLoaded srcWords init (p + 1) = srcWords.getD p 0 := by
  unfold lastLoaded
  simp

/-- Copying the next dword extends the copied prefix by one word. -/
private theorem copy_prefix_step (srcWords dstWords : List Word) (p : Nat)
    (hp : p < srcWords.length) (hd : dstWords.length = srcWords.length) :
    (srcWords.take p ++ dstWords.drop p).set p (srcWords.getD p 0)
      = srcWords.take (p + 1) ++ dstWords.drop (p + 1) := by
  induction p generalizing srcWords dstWords with
  | zero =>
    cases srcWords with
    | nil => exact absurd hp (by simp)
    | cons s st =>
      cases dstWords with
      | nil => simp at hd
      | cons d dt => rfl
  | succ k ih =>
    cases srcWords with
    | nil => exact absurd hp (by simp)
    | cons s st =>
      cases dstWords with
      | nil => simp at hd
      | cons d dt =>
        have hk : k < st.length := by simpa using hp
        have hdt : dt.length = st.length := by simpa using hd
        show (s :: (st.take k ++ dt.drop k)).set (k + 1) (List.getD (s :: st) (k + 1) 0)
            = s :: (st.take (k + 1) ++ dt.drop (k + 1))
        rw [List.set_cons_succ]
        simpa using ih st dt hk hdt

/-- Loop invariant for the flat `blsf_copy_quads` callee at remaining count `n`. -/
def copyInvF (src dst : Word) (srcWords dstWords : List Word) (init5 : Word) (n : Nat) : Assertion :=
  let p := 24 - n
  (.x5 ↦ᵣ lastLoaded srcWords init5 p)
    ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (8 * p)))
    ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (8 * p)))
    ** dwordsIs src srcWords
    ** dwordsIs dst (srcWords.take p ++ dstWords.drop p)

theorem pcFree_copyInvF (src dst : Word) (srcWords dstWords : List Word) (init5 : Word) (n : Nat) :
    (copyInvF src dst srcWords dstWords init5 n).pcFree := by
  unfold copyInvF
  pcf

private theorem blsfCopyLoopBody_spec (src dst : Word) (srcWords dstWords : List Word)
    (init5 : Word) (hs : srcWords.length = 24) (hd : dstWords.length = 24)
    (n : Nat) (hn : n < 24) :
    cpsTripleWithin 6 (0x8002eed4 : Word) (0x8002eed0 : Word) copy192Cr
      ((.x12 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** copyInvF src dst srcWords dstWords init5 (n + 1))
      ((.x12 ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** copyInvF src dst srcWords dstWords init5 n) := by
  have hpn : 24 - n = (24 - (n + 1)) + 1 := by omega
  set p := 24 - (n + 1) with hp
  set L := srcWords.take p ++ dstWords.drop p with hL
  have hsLen : p < srcWords.length := by rw [hs]; omega
  have hLlen : p < L.length := by
    rw [hL]
    simp only [List.length_append, List.length_take, List.length_drop, hs, hd]
    omega
  obtain ⟨sfront, srest, hsf, hsr, hsrcEq, _hsrcSet⟩ :=
    dwordsIs_at_set src srcWords p (srcWords.getD p 0) hsLen
  obtain ⟨dfront, drest, hdf, hdr, hdstEq, hdstSet⟩ :=
    dwordsIs_at_set dst L p (srcWords.getD p 0) hLlen
  have hset : L.set p (srcWords.getD p 0)
      = srcWords.take (p + 1) ++ dstWords.drop (p + 1) := by
    rw [hL]
    exact copy_prefix_step srcWords dstWords p hsLen (by rw [hs, hd])
  simp only [copyInvF, hpn, ← hp, ← hL]
  rw [hsrcEq, hdstEq, ← hset, hdstSet]
  have hld := ld_spec_gen_within .x5 .x10 (src + BitVec.ofNat 64 (8 * p))
    (lastLoaded srcWords init5 p) (srcWords.getD p 0) (0 : BitVec 12) (0x8002eed4 : Word)
    (by decide)
  rw [add_sext0] at hld
  rw [show (0x8002eed4 : Word) + 4 = (0x8002eed8 : Word) from by decide] at hld
  have hldC := liftCode (cr' := copy192Cr) hld (by code_mem)
  have hsd := sd_spec_gen_within .x11 .x5 (dst + BitVec.ofNat 64 (8 * p))
    (srcWords.getD p 0) (L.getD p 0) (0 : BitVec 12) (0x8002eed8 : Word)
  rw [add_sext0] at hsd
  rw [show (0x8002eed8 : Word) + 4 = (0x8002eedc : Word) from by decide] at hsd
  have hsdC := liftCode (cr' := copy192Cr) hsd (by code_mem)
  have ha0 := addi_spec_gen_same_within .x10 (src + BitVec.ofNat 64 (8 * p))
    (8 : BitVec 12) (0x8002eedc : Word) (by decide)
  rw [addr_step8] at ha0
  rw [show (0x8002eedc : Word) + 4 = (0x8002eee0 : Word) from by decide] at ha0
  have ha0C := liftCode (cr' := copy192Cr) ha0 (by code_mem)
  have ha1 := addi_spec_gen_same_within .x11 (dst + BitVec.ofNat 64 (8 * p))
    (8 : BitVec 12) (0x8002eee0 : Word) (by decide)
  rw [addr_step8] at ha1
  rw [show (0x8002eee0 : Word) + 4 = (0x8002eee4 : Word) from by decide] at ha1
  have ha1C := liftCode (cr' := copy192Cr) ha1 (by code_mem)
  have hcnt := addi_spec_gen_same_within .x12 (BitVec.ofNat 64 (n + 1))
    (-1 : BitVec 12) (0x8002eee4 : Word) (by decide)
  rw [cnt_step_down] at hcnt
  rw [show (0x8002eee4 : Word) + 4 = (0x8002eee8 : Word) from by decide] at hcnt
  have hcntC := liftCode (cr' := copy192Cr) hcnt (by code_mem)
  have hjal := jal_x0_spec_gen_within (-24 : BitVec 21) (0x8002eee8 : Word)
  rw [show (0x8002eee8 : Word) + signExtend21 (-24 : BitVec 21) = (0x8002eed0 : Word) from by decide] at hjal
  have hjalC := liftCode (cr' := copy192Cr) hjal (by code_mem)
  have hldF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (8 * p)))
      ** sfront ** srest ** dfront ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ L.getD p 0) ** drest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hsf
        | exact hsr
        | exact hdf
        | exact hdr) hldC
  have hsdF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (8 * p)))
      ** sfront ** ((src + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** srest
      ** dfront ** drest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hsf
        | exact hsr
        | exact hdf
        | exact hdr) hsdC
  have ha0F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ srcWords.getD p 0) ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (8 * p)))
      ** sfront ** ((src + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** srest
      ** dfront ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** drest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hsf
        | exact hsr
        | exact hdf
        | exact hdr) ha0C
  have ha1F := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 (n + 1)) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ srcWords.getD p 0) ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (8 * (p + 1))))
      ** sfront ** ((src + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** srest
      ** dfront ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** drest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hsf
        | exact hsr
        | exact hdf
        | exact hdr) ha1C
  have hcntF := cpsTripleWithin_frameR
    ((Reg.x0 ↦ᵣ (0 : Word)) ** (.x5 ↦ᵣ srcWords.getD p 0)
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (8 * (p + 1))))
      ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (8 * (p + 1))))
      ** sfront ** ((src + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** srest
      ** dfront ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** drest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hsf
        | exact hsr
        | exact hdf
        | exact hdr) hcntC
  have hjalF := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ BitVec.ofNat 64 n) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** (.x5 ↦ᵣ srcWords.getD p 0)
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 (8 * (p + 1))))
      ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 (8 * (p + 1))))
      ** sfront ** ((src + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** srest
      ** dfront ** ((dst + BitVec.ofNat 64 (8 * p)) ↦ₘ srcWords.getD p 0) ** drest)
    (by repeat first
        | apply pcFree_sepConj
        | exact pcFree_regIs
        | exact pcFree_memIs
        | exact hsf
        | exact hsr
        | exact hdf
        | exact hdr) hjalC
  have s1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hldF hsdF
  have s2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s1 ha0F
  have s3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s2 ha1F
  have s4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) s3 hcntF
  have s5 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by
    simpa only [sepConj_emp_left'] using hp) s4 hjalF
  refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => ?_) s5
  rw [lastLoaded_succ srcWords init5 p]
  have hq' := (sepConj_emp_left _).mp hq
  xperm_hyp hq'

/-- Flat whole-routine contract for the verified `blsf_copy_quads` callee, specialized to 24 quads. -/
theorem blsfCopyQuads24Flat_spec (ret src dst init5 : Word)
    (srcWords dstWords : List Word) (hs : srcWords.length = 24) (hd : dstWords.length = 24)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (24 * (6 + 1) + 1 + 1) (0x8002eed0 : Word) ret copy192Cr
      (((.x1 : Reg) ↦ᵣ ret) ** (.x5 ↦ᵣ init5) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
        ** (.x12 ↦ᵣ BitVec.ofNat 64 24) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** dwordsIs src srcWords ** dwordsIs dst dstWords)
      (((.x1 : Reg) ↦ᵣ ret) ** (.x5 ↦ᵣ lastLoaded srcWords init5 24)
        ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 192)) ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 192))
        ** (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** dwordsIs src srcWords ** dwordsIs dst srcWords) := by
  have hloop : cpsTripleWithin (24 * (6 + 1) + 1) (0x8002eed0 : Word) (0x8002eeec : Word)
      copy192Cr
      ((.x12 ↦ᵣ BitVec.ofNat 64 24) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** copyInvF src dst srcWords dstWords init5 24)
      ((.x12 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
        ** copyInvF src dst srcWords dstWords init5 0) := by
    have h := countdownLoop_spec copy192Cr (0x8002eed0 : Word) (0x8002eeec : Word)
      .x12 (28 : BitVec 13) 6 24 (copyInvF src dst srcWords dstWords init5)
      (by decide) (by omega) (by decide)
      (fun n => pcFree_copyInvF src dst srcWords dstWords init5 n)
      (by code_mem)
      (fun n hn => blsfCopyLoopBody_spec src dst srcWords dstWords init5 hs hd n hn)
    exact h
  have hstart : copyInvF src dst srcWords dstWords init5 24
      = ((.x5 ↦ᵣ init5) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
          ** dwordsIs src srcWords ** dwordsIs dst dstWords) := by
    simp [copyInvF, lastLoaded]
  have hend : copyInvF src dst srcWords dstWords init5 0
      = ((.x5 ↦ᵣ lastLoaded srcWords init5 24)
          ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 192))
          ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 192))
          ** dwordsIs src srcWords ** dwordsIs dst srcWords) := by
    simp [copyInvF]
    rw [List.take_of_length_le (by rw [hs]), show dstWords.drop 24 = [] from by rw [← hd]; exact List.drop_length,
        List.append_nil]
  rw [hstart, hend] at hloop
  have hloopF := cpsTripleWithin_frameR ((.x1 : Reg) ↦ᵣ ret) (by pcf) hloop
  have hret := Fn.jalr_ret_spec (0x8002eeec : Word) ret halign
    (P := (.x5 ↦ᵣ lastLoaded srcWords init5 24)
      ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 192)) ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 192))
      ** (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
      ** dwordsIs src srcWords ** dwordsIs dst srcWords)
    (by pcf)
  have hretC := liftCode (cr' := copy192Cr) hret (by code_mem)
  have s := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hloopF hretC
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) s

/-- Entry values of saved registers. -/
def copy192Vals (ret : Word) : Reg → Word :=
  fun r => match r with | .x1 => ret | _ => 0

/-- Post-body `ra` is the call link; epilogue restores entry `ra`. -/
def copy192Vals' : Reg → Word :=
  fun r => match r with | .x1 => (0x800335c4 : Word) | _ => 0

/-- Whole-routine ABI contract for `blsg2_copy192`. -/
theorem blsg2Copy192Frame_spec (sp0 ret src dst init5 v12 : Word)
    (srcWords dstWords : List Word) (hs : srcWords.length = 24) (hd : dstWords.length = 24)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin (1 + copy192Frame.length + (1 + (1 + (24 * (6 + 1) + 1 + 1)))
        + copy192Frame.length + 1 + 1)
      (0x800335b4 : Word) ret copy192Cr
      ((.x2 ↦ᵣ sp0) ** regsAt copy192Frame (copy192Vals ret)
        ** frameSlotsOwn copy192Frame (sp0 + signExtend12 (-16 : BitVec 12))
        ** ((.x5 ↦ᵣ init5) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** (.x12 ↦ᵣ v12)
          ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs src srcWords ** dwordsIs dst dstWords))
      ((.x2 ↦ᵣ sp0) ** regsAt copy192Frame (copy192Vals ret)
        ** frameSlotsSaved copy192Frame (sp0 + signExtend12 (-16 : BitVec 12))
            (copy192Vals ret)
        ** ((.x5 ↦ᵣ lastLoaded srcWords init5 24)
          ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 192)) ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 192))
          ** (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
          ** dwordsIs src srcWords ** dwordsIs dst srcWords)) := by
  have hli := li_spec_gen_within .x12 v12 (24 : Word) (0x800335bc : Word) (by decide)
  rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl] at hli
  rw [show (0x800335bc : Word) + 4 = (0x800335c0 : Word) from by decide] at hli
  have hliC := liftCode (cr' := copy192Cr) hli (by code_mem)
  have hliF := cpsTripleWithin_frameR
    (((.x1 : Reg) ↦ᵣ ret) ** (.x5 ↦ᵣ init5) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst)
      ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs src srcWords ** dwordsIs dst dstWords)
    (by pcf) hliC
  have hcallee := blsfCopyQuads24Flat_spec ((0x800335c0 : Word) + 4) src dst init5
    srcWords dstWords hs hd (by decide)
  have hcall := callWithin_spec (0x800335c0 : Word) (0x8002eed0 : Word) ret
    (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_copy192 + 12))
    (24 * (6 + 1) + 1 + 1)
    (by decide) (by code_mem) (by pcf) hcallee
  rw [show (0x800335c0 : Word) + 4 = (0x800335c4 : Word) from by decide] at hcall
  have hbodyCore := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hliF hcall
  have hbody : cpsTripleWithin (1 + (1 + (24 * (6 + 1) + 1 + 1)))
      ((0x800335b4 : Word) + BitVec.ofNat 64 (4 * (1 + copy192Frame.length)))
      ((0x800335b4 : Word) + BitVec.ofNat 64 (4 * (1 + copy192Frame.length + copy192Body.length)))
      copy192Cr
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** regsAt copy192Frame (copy192Vals ret)
        ** frameSlotsSaved copy192Frame (sp0 + signExtend12 (-16 : BitVec 12))
            (copy192Vals ret)
        ** ((.x5 ↦ᵣ init5) ** (.x10 ↦ᵣ src) ** (.x11 ↦ᵣ dst) ** (.x12 ↦ᵣ v12)
          ** (Reg.x0 ↦ᵣ (0 : Word)) ** dwordsIs src srcWords ** dwordsIs dst dstWords))
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** regsAt copy192Frame copy192Vals'
        ** frameSlotsSaved copy192Frame (sp0 + signExtend12 (-16 : BitVec 12))
            (copy192Vals ret)
        ** ((.x5 ↦ᵣ lastLoaded srcWords init5 24)
          ** (.x10 ↦ᵣ (src + BitVec.ofNat 64 192)) ** (.x11 ↦ᵣ (dst + BitVec.ofNat 64 192))
          ** (.x12 ↦ᵣ BitVec.ofNat 64 0) ** (Reg.x0 ↦ᵣ (0 : Word))
          ** dwordsIs src srcWords ** dwordsIs dst srcWords)) := by
    have hentry : (0x800335b4 : Word) + BitVec.ofNat 64 (4 * (1 + copy192Frame.length))
        = (0x800335bc : Word) := by decide
    have hexit : (0x800335b4 : Word)
          + BitVec.ofNat 64 (4 * (1 + copy192Frame.length + copy192Body.length))
        = (0x800335c4 : Word) := by decide
    rw [hentry, hexit]
    simp only [copy192Frame, regsAt, frameSlotsSaved, copy192Vals, copy192Vals',
      List.foldr_cons, List.foldr_nil, sepConj_emp_right']
    have hchainF := cpsTripleWithin_frameR
      ((.x2 ↦ᵣ (sp0 + signExtend12 (-16 : BitVec 12)))
        ** (((sp0 + signExtend12 (-16 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ ret))
      (by pcf) hbodyCore
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hq => by xperm_hyp hq) hchainF
  abi_frame (16 : BitVec 12) halign hbody

end Bls12G2Copy192SAsm

end EvmAsm.Codegen
