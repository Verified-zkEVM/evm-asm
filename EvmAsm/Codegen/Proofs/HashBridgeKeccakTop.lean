/-
  EvmAsm.Codegen.Proofs.HashBridgeKeccakTop

  Top triple `zkvm_keccak256_spec_within` via no-ra frame + body_spec.

  PR note: outer absorb uses `signedCountdownLoop_reload_spec` (hdr=LI at
  0x8000368c). The BLT-header `signedCountdownLoop_spec` does NOT apply
  (JAL target LI ≠ BLT at 0x80003690).
-/

import EvmAsm.Codegen.Proofs.HashBridgeKeccakBody
import EvmAsm.Codegen.Proofs.HashBridgeKeccakFrame
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Rv64.Tactics.XPermChunked

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_keccak256
private abbrev Zk3 : Word := BitVec.ofNat 64 GuestAddrs.zk3_state
private abbrev keccakProgL : List Instr := zkvmKeccak256_prog
private abbrev keccakCr : CodeReq := CodeReq.ofProg B keccakProgL

private theorem keccakProgL_len : keccakProgL.length = 69 := by
  simp only [keccakProgL, zkvmKeccak256_prog, zkvmKeccak256_prog_of]
  decide

private theorem keccakProgL_bound : 4 * keccakProgL.length < 2 ^ 64 := by
  rw [keccakProgL_len]; norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < keccakProgL.length)
    (hins : keccakProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → keccakCr a = some i :=
  fun a i h =>
    CodeReq.ofProg_mem_at B A keccakProgL k ins hA hk hins keccakProgL_bound a i h

/-- Caller ambient at entry (no frame regs x8/x9/x18/x20). -/
def keccakCallerPre (inputBase lenW outputBase : Word)
    (v28 v29 : Word) (os input out0 : List (BitVec 8))
    (A : Assertion) : Assertion :=
  (.x10 ↦ᵣ inputBase) ** (.x11 ↦ᵣ lenW) ** (.x12 ↦ᵣ outputBase) **
    (.x28 ↦ᵣ v28) ** (.x29 ↦ᵣ v29) **
    (.x0 ↦ᵣ (0 : Word)) **
    regOwns keccakBodyFreeTemps **
    bytesRegion Zk3 os **
    bytesRegion inputBase input **
    bytesRegion outputBase out0 ** A

theorem keccakCallerPre_pcFree (inputBase lenW outputBase : Word)
    (v28 v29 : Word) (os input out0 : List (BitVec 8))
    (A : Assertion) (hA : A.pcFree) :
    (keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A).pcFree := by
  simp only [keccakCallerPre]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Caller free A: input residual+prefix only (frame owns x9/x20 separately). -/
def keccakCallerFreeA (inputBase : Word) (input : List (BitVec 8)) (N : Nat)
    (A : Assertion) : Assertion :=
  bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
    bytesRegion inputBase (input.take (keccakAbsorbStep * N)) ** A

theorem keccakCallerFreeA_pcFree (inputBase : Word) (input : List (BitVec 8))
    (N : Nat) (A : Assertion) (hA : A.pcFree) :
    (keccakCallerFreeA inputBase input N A).pcFree :=
  pcFree_sepConj (bytesRegion_pcFree _ _) <|
  pcFree_sepConj (bytesRegion_pcFree _ _) hA

/-- Caller post: a0=0, digest written, sponge final; frame owns separate. -/def keccakCallerPost (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) : Assertion :=
  (regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
    bytesRegion Zk3
      (setBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0
        (keccakBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0)) **
    bytesRegion outputBase (keccakBodyDigest input N rem) **
    ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 **
      keccakCallerFreeA inputBase input N A)

theorem keccakCallerPost_pcFree (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (A : Assertion) (hA : A.pcFree) :
    (keccakCallerPost inputBase outputBase input N rem A).pcFree := by
  simp only [keccakCallerPost]
  exact pcFree_sepConj (by pcf) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (bytesRegion_pcFree _ _) <|
    pcFree_sepConj (by pcf) <|
    pcFree_sepConj (pcFree_regOwns _) <|
    keccakCallerFreeA_pcFree _ _ _ _ hA

/-- Entry vals for frame regs. -/
def keccakEntryVals (v8 v9 v18 v20 : Word) : Reg → Word
  | .x8 => v8
  | .x9 => v9
  | .x18 => v18
  | .x20 => v20
  | _ => (0 : Word)

/-- Flat frame regs (no trailing emp). -/
private abbrev frameRegsIs (v8 v9 v18 v20 : Word) : Assertion :=
  (.x8 ↦ᵣ v8) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ v18) ** (.x20 ↦ᵣ v20)

private abbrev frameRegsOwn : Assertion :=
  (regOwn .x8) ** (regOwn .x9) ** (regOwn .x18) ** (regOwn .x20)

/-- foldr regsAt = flat frame regs (emp stripped). -/
private theorem regsAt_flat (v8 v9 v18 v20 : Word) :
    regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) =
      frameRegsIs v8 v9 v18 v20 := by
  simp only [frameRegsIs, keccakFrame, regsAt, keccakEntryVals, List.foldr,
    sepConj_emp_right']

private theorem regsOwnAt_flat :
    regsOwnAt keccakFrame = frameRegsOwn := by
  simp only [frameRegsOwn, keccakFrame, regsOwnAt, List.foldr,
    sepConj_emp_right']

/-- regsAt+callerPre → bodyEntryPre (holds). -/
private theorem entryCore_to_body (h : PartialState)
    (inputBase lenW outputBase : Word)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os input out0 : List (BitVec 8)) (A : Assertion)
    (hp :
      (regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A) h) :
    keccakBodyEntryPre inputBase lenW outputBase v20 v9 v18 v8 v28 v29
      os input out0 A h := by
  have hp1 :
      (frameRegsIs v8 v9 v18 v20 **
        keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A) h := by
    simpa [regsAt_flat] using hp
  simp only [frameRegsIs, keccakCallerPre, keccakBodyEntryPre] at hp1 ⊢
  xperm_chunked hp1

/-- bodyExitPost padFree → regsOwn+callerPost (holds). -/
private theorem exitCore_to_caller (h : PartialState)
    (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat) (A : Assertion)
    (hp :
      keccakBodyExitPost outputBase input N rem
        (keccakPadFreeA inputBase input N A) h) :
    (regsOwnAt keccakFrame **
      keccakCallerPost inputBase outputBase input N rem A) h := by
  -- Fully unfold exit+padFree, then drop x8/x18, then xperm
  have hp0 :
      ((.x8 ↦ᵣ Zk3) ** (.x18 ↦ᵣ outputBase) **
        (regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion Zk3
          (setBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0)) **
        bytesRegion outputBase (keccakBodyDigest input N rem) **
        ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 **
          (bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
            bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
            (regOwn .x9) ** (regOwn .x20) ** A))) h := by
    simpa [keccakBodyExitPost, keccakPadFreeA] using hp
  have hp1 :
      ((regOwn .x8) ** (regOwn .x18) **
        (regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
        bytesRegion Zk3
          (setBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0
            (keccakBytes (keccakGuestPad (keccakBodyPrePad input N rem) rem) 0)) **
        bytesRegion outputBase (keccakBodyDigest input N rem) **
        ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 **
          (bytesRegion (keccakAbsorbCursor inputBase N) (keccakResidual input N) **
            bytesRegion inputBase (input.take (keccakAbsorbStep * N)) **
            (regOwn .x9) ** (regOwn .x20) ** A))) h := by
    refine sepConj_mono (regIs_implies_regOwn (r := .x8)) ?_ h hp0
    intro h1 hp1
    exact sepConj_mono (regIs_implies_regOwn (r := .x18)) (fun _ => id) h1 hp1
  have hp2 :
      (frameRegsOwn **
        keccakCallerPost inputBase outputBase input N rem A) h := by
    simp only [frameRegsOwn, keccakCallerPost, keccakCallerFreeA] at hp1 ⊢
    xperm_chunked hp1
  simpa [regsOwnAt_flat] using hp2

/-- Framed body for no-ra wrap. -/
theorem keccakBody_framed (sp0 ret : Word)
    (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem → Zk3.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess (Zk3 + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (Zk3 + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true) :
    let newSp := sp0 + signExtend12 ((-32 : BitVec 12))
    let vals := keccakEntryVals v8 v9 v18 v20
    let lenW := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
    let out0 := List.replicate 32 (0 : BitVec 8)
    cpsTripleWithin (keccakBodyFuel N rem)
      (keccakBodyEntry B) (keccakBodyExit B) keccakCr
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame newSp vals **
        keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A)
      ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
        regsOwnAt keccakFrame **
        frameSlotsSaved keccakFrame newSp vals **
        keccakCallerPost inputBase outputBase input N rem A) := by
  intro newSp vals lenW out0
  have hbody0 := keccakBody_spec inputBase outputBase input N rem
    v20 v9 v18 v8 v28 v29 os A hA
    hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hslots : (frameSlotsSaved keccakFrame newSp vals).pcFree :=
    pcFree_frameSlotsSaved _ _ _
  -- frameR: bodyEntry → bodyExit becomes bodyEntry ** F / bodyExit ** F
  -- where F = x2 ** x1 ** slots
  have hbodyF := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
      frameSlotsSaved keccakFrame newSp vals)
    (pcFree_sepConj (by pcf) (pcFree_sepConj (by pcf) hslots))
    hbody0
  -- Reshape theorem pre/post ↔ bodyEntry ** F / owns+caller ** F
  refine cpsTripleWithin_weaken
    (fun h hp => by
      -- hp : x2 ** x1 ** regsAt ** slots ** callerPre
      -- need : bodyEntry ** (x2 ** x1 ** slots)
      have hp1 :
          ((regsAt keccakFrame vals **
              keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
              frameSlotsSaved keccakFrame newSp vals)) h := by
        xperm_hyp hp
      refine sepConj_mono ?_ (fun _ => id) h hp1
      intro h1 hp1'
      exact entryCore_to_body h1 inputBase lenW outputBase
        v8 v9 v18 v20 v28 v29 os input out0 A (by simpa [vals] using hp1'))
    (fun h hq => by
      -- hq : bodyExit ** (x2 ** x1 ** slots)
      -- need : x2 ** x1 ** regsOwn ** slots ** callerPost
      have hq1 :
          ((regsOwnAt keccakFrame **
              keccakCallerPost inputBase outputBase input N rem A) **
            ((.x2 ↦ᵣ newSp) ** (.x1 ↦ᵣ ret) **
              frameSlotsSaved keccakFrame newSp vals)) h := by
        refine sepConj_mono ?_ (fun _ => id) h hq
        intro h1 hp1
        exact exitCore_to_caller h1 inputBase outputBase input N rem A
          (by simpa using hp1)
      xperm_hyp hq1)
    hbodyF

/-- Top triple for `zkvm_keccak256`.
    Outer loop uses LI-header reload (`signedCountdownLoop_reload_spec`);
    BLT-header lemma does not apply (JAL→LI 0x8000368c ≠ BLT 0x80003690). -/
theorem zkvm_keccak256_spec_within (sp0 ret : Word)
    (inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : Zk3.toNat % 8 = 0)
    (hover : Zk3.toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem → Zk3.toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess (Zk3 + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess (Zk3 + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess (Zk3 + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr (Zk3 + BitVec.ofNat 64 j) = true) :
    let vals := keccakEntryVals v8 v9 v18 v20
    let lenW := BitVec.ofNat 64 (keccakAbsorbStep * N + rem)
    let out0 := List.replicate 32 (0 : BitVec 8)
    let newSp := sp0 + signExtend12 ((-32 : BitVec 12))
    cpsTripleWithin (5 + keccakBodyFuel N rem + 6) B ret keccakCr
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsOwn keccakFrame newSp **
        keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        regsAt keccakFrame vals **
        frameSlotsSaved keccakFrame newSp vals **
        keccakCallerPost inputBase outputBase input N rem A) := by
  intro vals lenW out0 newSp
  have hbody := keccakBody_framed sp0 ret inputBase outputBase input N rem
    v8 v9 v18 v20 v28 v29 os A hA
    hlen hrem_le hos halign_zk hover hNbound hrem64 hb8i
    hovers hoveri hvalids hvalidi hvalidRem hvalid135 hvalidMem
  refine keccakFrame_spec_own keccakCr B sp0 ret vals (keccakBodyFuel N rem)
    (keccakCallerPre inputBase lenW outputBase v28 v29 os input out0 A)
    (keccakCallerPost inputBase outputBase input N rem A)
    halign_ret
    (keccakCallerPre_pcFree _ _ _ _ _ _ _ _ _ hA)
    (keccakCallerPost_pcFree _ _ _ _ _ _ hA)
    (mem_at 0 (.ADDI .x2 .x2 (-32 : BitVec 12)) B
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    ?hmemS ?hmemL
    (mem_at 67 (.ADDI .x2 .x2 (32 : BitVec 12)) (B + 268)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    (mem_at 68 (.JALR .x0 .x1 (0 : BitVec 12)) (B + 272)
      (by decide) (by rw [keccakProgL_len]; norm_num) (by rfl))
    ?hbody
  · -- store prog at base+4
    intro a i h
    have hsub := CodeReq.ofProg_mono_subrange B
      [(.ADDI .x2 .x2 (-32 : BitVec 12))]
      (storeProg keccakFrame)
      (keccakProgL.drop 5)
      (by
        have : keccakProgL =
            [(.ADDI .x2 .x2 (-32 : BitVec 12))] ++ storeProg keccakFrame ++
              keccakProgL.drop 5 := by
          simp only [keccakProgL, zkvmKeccak256_prog, zkvmKeccak256_prog_of,
            storeProg, keccakFrame]
          decide
        rw [← this]; exact keccakProgL_bound)
      a i h
    exact hsub
  · -- load prog at body exit base+252
    intro a i h
    have hsub := CodeReq.ofProg_mono_subrange B
      (keccakProgL.take 63)
      (loadProg keccakFrame)
      (keccakProgL.drop 67)
      (by
        have : keccakProgL =
            keccakProgL.take 63 ++ loadProg keccakFrame ++
              keccakProgL.drop 67 := by
          simp only [keccakProgL, zkvmKeccak256_prog, zkvmKeccak256_prog_of,
            loadProg, keccakFrame]
          decide
        rw [← this]; exact keccakProgL_bound)
      a i (by
        -- startA = bodyExit = B+252 = B+4*63
        have hA : keccakBodyExit B = B + BitVec.ofNat 64 (4 * 63) := by
          simp only [keccakBodyExit]
          decide
        -- ofProg at bodyExit vs ofProg at B+(take 63)
        -- mono_subrange expects ofProg (B + 4*|pre|) mid
        have : CodeReq.ofProg (B + BitVec.ofNat 64 (4 * (keccakProgL.take 63).length))
            (loadProg keccakFrame) a = some i := by
          have hlen : (keccakProgL.take 63).length = 63 := by
            simp only [List.length_take, keccakProgL_len]; norm_num
          simpa [hlen, hA, keccakBodyExit] using h
        exact this)
    exact hsub
  · -- body: PC pins bodyEntry/Exit = B+20 / B+252
    simpa [keccakBodyEntry, keccakBodyExit, newSp, vals, lenW, out0] using hbody

end EvmAsm.Codegen.Proofs
