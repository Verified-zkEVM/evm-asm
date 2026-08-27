/-
  EvmAsm.Codegen.Programs.BlockHashFromHeaderSpec

  Whole-routine contract for `block_hash_from_header`: the six-instruction
  caller frame around `zkvm_keccak256`.
-/

import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Proofs.HashBridgeKeccakTop
import EvmAsm.Codegen.Proofs.HashBridgeKeccakBridge
import EvmAsm.Rv64.SAsm.AbiFrameCall
import EvmAsm.Rv64.SAsm.TwoExitLoop
import EvmAsm.Stateless.SpecRef.BlocksRlp
import EvmAsm.Stateless.SpecRef.HeaderRoundTrip

namespace EvmAsm.Codegen.BlockHashFromHeaderSpec

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.Proofs

abbrev B : Word := (GuestAddrs.block_hash_from_header : Word)
abbrev K : Word := (GuestAddrs.zkvm_keccak256 : Word)
abbrev wrapperCode : CodeReq := CodeReq.ofProg B blockHashFromHeader_prog
abbrev keccakCode : CodeReq := CodeReq.ofProg K zkvmKeccak256_prog
abbrev fullCode : CodeReq := wrapperCode.union keccakCode

theorem wrapper_length : blockHashFromHeader_prog.length = 6 := by decide

theorem wrapper_mem : ∀ a i,
    wrapperCode a = some i → fullCode a = some i := by
  intro a i h
  exact CodeReq.union_mono_left a i h

theorem keccak_mem : ∀ a i,
    keccakCode a = some i → fullCode a = some i := by
  intro a i h
  exact CodeReq.mono_union_right
    (CodeReq.Disjoint.ofProg_ranges B K blockHashFromHeader_prog
      zkvmKeccak256_prog
      (by rw [wrapper_length]; decide)
      (by decide)
      (by rw [wrapper_length]; decide))
    (fun _ _ h => h) a i h

theorem call_mem : ∀ a i,
    CodeReq.singleton (B + 8) (.JAL .x1
      (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_hash_from_header + 8))) a = some i →
      fullCode a = some i := by
  intro a i h
  have hw : wrapperCode a = some i := by
    exact CodeReq.ofProg_mem_at B (B + 8) blockHashFromHeader_prog 2
      (.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_hash_from_header + 8)))
      (by decide) (by rw [wrapper_length]; decide) rfl (by rw [wrapper_length]; decide) a i h
  exact wrapper_mem a i hw

theorem stackFree4_eq_keccakFrameSlotsOwn (sp : Word) :
    stackFree sp 4 =
      frameSlotsOwn keccakFrame (sp + signExtend12 (-32 : BitVec 12)) := by
  show (memOwn (sp - BitVec.ofNat 64 (8 * 4)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 3)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 2)) **
      memOwn (sp - BitVec.ofNat 64 (8 * 1)) ** empAssertion) = _
  show _ = (memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (8 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (16 : BitVec 12)) **
      memOwn ((sp + signExtend12 (-32 : BitVec 12)) +
          signExtend12 (24 : BitVec 12)) ** empAssertion)
  rw [show signExtend12 (-32 : BitVec 12) = (-32 : Word) from by decide,
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (8 : BitVec 12) = (8 : Word) from by decide,
    show signExtend12 (16 : BitVec 12) = (16 : Word) from by decide,
    show signExtend12 (24 : BitVec 12) = (24 : Word) from by decide,
    show sp - BitVec.ofNat 64 (8 * 4) = sp + (-32 : Word) + (0 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 3) = sp + (-32 : Word) + (8 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 2) = sp + (-32 : Word) + (16 : Word) from by bv_omega,
    show sp - BitVec.ofNat 64 (8 * 1) = sp + (-32 : Word) + (24 : Word) from by bv_omega]

set_option maxRecDepth 8000 in
theorem block_hash_from_header_spec_within
    (sp0 ret inputBase outputBase : Word)
    (input : List (BitVec 8)) (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : input.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (6 + (5 + keccakBodyFuel N rem + 6)) B ret fullCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        memOwn (sp0 + signExtend12 (-16 : BitVec 12)) **
        stackFree (sp0 + signExtend12 (-16 : BitVec 12)) 4 **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
          v28 v29 os input (List.replicate 32 (0 : BitVec 8)) A)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        ((sp0 + signExtend12 (-16 : BitVec 12)) ↦ₘ ret) **
        frameSlotsSaved keccakFrame
          (sp0 + signExtend12 (-16 : BitVec 12) +
            signExtend12 (-32 : BitVec 12))
          (keccakEntryVals v8 v9 v18 v20) **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPost inputBase outputBase input N rem A) := by
  let spC := sp0 + signExtend12 (-16 : BitVec 12)
  let out0 := List.replicate 32 (0 : BitVec 8)
  have hcallee := zkvm_keccak256_spec_within spC (B + 12)
    inputBase outputBase input N rem out0 v8 v9 v18 v20 v28 v29 os A hA
    (by decide) hlen hrem_le (by simp [out0]) hos halign_zk hover hNbound
    hrem64 hb8i hovers hoveri
    hvalids hvalidi hvalidRem hvalid135 hvalidMem
  have hcallee' :
      cpsTripleWithin (5 + keccakBodyFuel N rem + 6) K (B + 12) keccakCode
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (B + 12)) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
          frameSlotsOwn keccakFrame
            (spC + signExtend12 (-32 : BitVec 12)) **
          keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
            v28 v29 os input out0 A)
        ((.x2 ↦ᵣ spC) ** (.x1 ↦ᵣ (B + 12)) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
          frameSlotsSaved keccakFrame
            (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals v8 v9 v18 v20) **
          keccakCallerPost inputBase outputBase input N rem A) := by
    rw [← hlen] at hcallee
    simpa [B, K, keccakCode, spC, out0] using hcallee
  rw [← stackFree4_eq_keccakFrameSlotsOwn spC] at hcallee'
  have hcalleeFull :
      cpsTripleWithin (5 + keccakBodyFuel N rem + 6) K (B + 12) fullCode
        ((.x1 ↦ᵣ (B + 12)) ** (.x2 ↦ᵣ spC) **
          (stackFree spC 4 **
            regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
            keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
              v28 v29 os input out0 A))
        ((.x1 ↦ᵣ (B + 12)) ** (.x2 ↦ᵣ spC) **
          (frameSlotsSaved keccakFrame
              (spC + signExtend12 (-32 : BitVec 12))
              (keccakEntryVals v8 v9 v18 v20) **
            regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
            keccakCallerPost inputBase outputBase input N rem A)) := by
    have h := cpsTripleWithin_extend_code keccak_mem hcallee'
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => by xperm_hyp hq) h
  have hcallPc : B + 8 + (4 : Word) = B + 12 := by bv_omega
  have hcall := abiFrameCall_spec (cr := fullCode)
    (calleePre := stackFree spC 4 **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
        v28 v29 os input out0 A)
    (calleePost := frameSlotsSaved keccakFrame
        (spC + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals v8 v9 v18 v20) **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase outputBase input N rem A)
    (F := frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
      (fun r => if r = .x1 then ret else 0)) (B + 8) K ret spC
    (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_hash_from_header + 8))
    0 (5 + keccakBodyFuel N rem + 6)
    (by decide)
    call_mem
    (pcFree_sepConj (pcFree_stackFree _ _)
      (pcFree_sepConj
        (pcFree_regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20))
        (keccakCallerPre_pcFree inputBase
          (BitVec.ofNat 64 input.length) outputBase v28 v29 os input out0 A hA)))
    (pcFree_frameSlotsSaved _ _ _)
    (by
      simpa only [hcallPc, stackFree_zero, sepConj_emp_left', sepConj_emp_right']
        using hcalleeFull)
  simp only [stackFree_zero, sepConj_emp_left'] at hcall
  rw [hcallPc] at hcall
  have hpreF : (stackFree spC 4 **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
        v28 v29 os input out0 A).pcFree := by
    exact pcFree_sepConj (pcFree_stackFree _ _)
      (pcFree_sepConj
        (pcFree_regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20))
        (keccakCallerPre_pcFree inputBase
          (BitVec.ofNat 64 input.length) outputBase v28 v29 os input out0 A hA))
  have hpostF : (frameSlotsSaved keccakFrame
      (spC + signExtend12 (-32 : BitVec 12))
      (keccakEntryVals v8 v9 v18 v20) **
      regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase outputBase input N rem A).pcFree := by
    exact pcFree_sepConj (pcFree_frameSlotsSaved _ _ _)
      (pcFree_sepConj
        (pcFree_regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20))
        (keccakCallerPost_pcFree inputBase outputBase input N rem A hA))
  have hprogBound :
      4 * (abiFrameProg (-16 : BitVec 12) (16 : BitVec 12)
        [(.x1, (0 : BitVec 12))]
        [.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256
          (GuestAddrs.block_hash_from_header + 8))]).length < 2 ^ 64 := by
    norm_num [abiFrameProg, framePrologue, frameEpilogue, storeProg, loadProg]
  have hframe := abiFrame_spec_own B sp0 ret
    (-16 : BitVec 12) (16 : BitVec 12) [(.x1, (0 : BitVec 12))] 0 []
    (fun r => if r = .x1 then ret else 0)
    [.JAL .x1 (jalOff GuestAddrs.zkvm_keccak256 (GuestAddrs.block_hash_from_header + 8))]
    (1 + (5 + keccakBodyFuel N rem + 6))
    (stackFree spC 4 ** regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPre inputBase (BitVec.ofNat 64 input.length) outputBase
        v28 v29 os input out0 A)
    (frameSlotsSaved keccakFrame
        (spC + signExtend12 (-32 : BitVec 12))
        (keccakEntryVals v8 v9 v18 v20) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
      keccakCallerPost inputBase outputBase input N rem A)
    fullCode rfl (by decide) (by decide) hprogBound (by simp)
    halign_ret (by
      have hneg : signExtend12 (-16 : BitVec 12) = BitVec.ofInt 64 (-16) := by decide
      have hpos : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
      rw [hneg, hpos, BitVec.add_assoc]
      bv_omega) hpreF hpostF
    (by
      intro a i h
      exact wrapper_mem a i h)
    (by
      refine cpsTripleWithin_weaken (fun _ hp => by
        simp [spC, regsAt, frameSlotsSaved, List.foldr, sepConj_emp_right'] at hp ⊢
        xperm_hyp hp) ?_ hcall
      intro a hq
      have hq1 :
          ((.x1 ↦ᵣ (B + 12)) **
            ((.x2 ↦ᵣ spC) **
              (frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
                (fun r => if r = .x1 then ret else 0) **
                frameSlotsSaved keccakFrame
                  (spC + signExtend12 (-32 : BitVec 12))
                  (keccakEntryVals v8 v9 v18 v20) **
                regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
                keccakCallerPost inputBase outputBase input N rem A))) a := by
        xperm_hyp hq
      have hq2 := sepConj_mono_left
        (regIs_to_regOwn .x1 (B + 12)) a hq1
      have hq3 :
          ((.x2 ↦ᵣ spC) ** regOwn .x1 **
        (frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
          (fun r => if r = .x1 then ret else 0) **
          frameSlotsSaved keccakFrame
            (spC + signExtend12 (-32 : BitVec 12))
            (keccakEntryVals v8 v9 v18 v20) **
          regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
          keccakCallerPost inputBase outputBase input N rem A)) a := by
        xperm_hyp hq2
      simpa [spC, regsOwnAt, regsAt, frameSlotsSaved, List.foldr,
        sepConj_emp_right'] using hq3)
  have hframeOwn :
      frameSlotsOwn [(.x1, (0 : BitVec 12))] spC = memOwn spC := by
    simp only [frameSlotsOwn, List.foldr, sepConj_emp_right']
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    exact congrArg memOwn (BitVec.add_zero spC)
  have hframeSaved :
      frameSlotsSaved [(.x1, (0 : BitVec 12))] spC
        (fun r => if r = .x1 then ret else 0) = (spC ↦ₘ ret) := by
    simp only [frameSlotsSaved, List.foldr, sepConj_emp_right']
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide]
    simp
  rw [hframeOwn, hframeSaved] at hframe
  have hsteps :
      1 + [(Reg.x1, (0 : BitVec 12))].length +
          (1 + (5 + keccakBodyFuel N rem + 6)) +
          [(Reg.x1, (0 : BitVec 12))].length + 1 + 1 =
        6 + (5 + keccakBodyFuel N rem + 6) := by
    simp
    omega
  rw [hsteps] at hframe
  simpa [spC, out0, blockHashFromHeader_prog, abiFrameProg, framePrologue,
    frameEpilogue, regsAt, regsOwnAt, stackFree, keccakEntryVals,
    sepConj_emp_right'] using hframe

/-! ## The binding to `SpecRef.headerHash` (#12223)

    `block_hash_from_header_spec_within` states its post as
    `keccakBodyDigest input N rem` — the digest of WHATEVER bytes the caller put
    at `inputBase`. `SpecRef.headerHash h` is by definition
    `keccak256 (RLP.encode (headerToRlpItem h))`, so instantiating the triple at
    those bytes turns the output cell into the reference header hash.

    ### What is closed, and how the seam is discharged

    Two legs, both kernel-checked, composed below into
    `block_hash_from_header_headerHash_within`:

    * the HASH leg, `keccakBodyDigest_encode_eq_headerHash` (#12644, this file):
      the guest's sponge model applied to a header's RLP encoding IS
      `SpecRef.headerHash`. Unconditional.
    * the CANONICALITY leg, `SpecRef.encode_headerToRlpItem_of_decode`
      (#12647, `SpecRef/HeaderRoundTrip.lean`): bytes that `_decode_header`
      ACCEPTS are exactly the encoding of the header it returns. Its only
      hypothesis is that the decode accepts.

    ⚠️ AN EARLIER VERSION OF THIS NOTE WAS WRONG about what remained, and the
    error is worth recording because it mis-scoped the issue for a while. It
    said a "RE-ENCODE leg" was open — "nothing here proves the guest CONSTRUCTS
    that encoding from header fields". **The guest never constructs the header
    RLP.** `block_hash_from_header` hashes bytes handed to it from the witness,
    and the guest *decodes* those bytes (`header_extended_decode`, rowed
    `.proven`). So the seam is not a construction obligation at all: the
    hypothesis "the bytes at `inputBase` are the header's encoding" is
    DISCHARGED from the decode, by the canonicality leg. That is what the
    composition below does — it takes `_decode_header hb = .ok hdr` as the
    hypothesis and never mentions the encoding.

    ### What genuinely remains

    The composed theorem still takes `_decode_header hb = .ok hdr` as an
    assumption about the caller's buffer. Tying it to the guest's own decoder —
    i.e. that the machine-level `header_extended_decode` at `inputBase` agrees
    with `SpecRef._decode_header` on the same bytes, so that a guest execution
    supplies this hypothesis rather than the specification consumer — is a
    separate correspondence obligation on that routine and is NOT claimed here.
    Nor is the surrounding block-hash *search* (`blockhash_from_witness_headers`
    is `.conditional`, empty-section arm only). -/

/-- The digest of a header's RLP encoding IS the reference header hash.
    Unconditional — `keccakBodyDigest_div_eq_specref` recovers `N`/`rem` from the
    length, and `headerHash` is `keccak256 ∘ encode ∘ headerToRlpItem` by
    definition. -/
theorem keccakBodyDigest_encode_eq_headerHash
    (h : EvmAsm.Stateless.SpecRef.Header) :
    keccakBodyDigest (EvmAsm.EL.RLP.encode (EvmAsm.Stateless.SpecRef.headerToRlpItem h))
        ((EvmAsm.EL.RLP.encode
          (EvmAsm.Stateless.SpecRef.headerToRlpItem h)).length / 136)
        ((EvmAsm.EL.RLP.encode
          (EvmAsm.Stateless.SpecRef.headerToRlpItem h)).length % 136)
      = EvmAsm.Stateless.SpecRef.headerHash h := by
  rw [keccakBodyDigest_div_eq_specref]
  rfl

/-- ⭐ **The seam, discharged from the DECODE.** The digest of bytes that
    `_decode_header` accepts is the reference hash of the header it returned —
    no "the bytes are the encoding" hypothesis survives.

    This is the two legs of #12223 in one line: the canonicality leg
    (`SpecRef.encode_headerToRlpItem_of_decode`) rewrites `hb` into
    `encode (headerToRlpItem hdr)`, and the hash leg
    (`keccakBodyDigest_eq_specref`) turns the guest sponge model into
    `SpecRef.keccak256`, which is `headerHash` by definition.

    `N`/`rem` are left general rather than fixed to `hb.length / 136` and
    `hb.length % 136`, because that is the shape
    `block_hash_from_header_spec_within` carries: the caller's length partition
    is an ABI fact, not an input-domain gate. -/
theorem keccakBodyDigest_eq_headerHash_of_decode
    {hb : List (BitVec 8)} {hdr : EvmAsm.Stateless.SpecRef.Header}
    (hdec : EvmAsm.Stateless.SpecRef._decode_header hb = .ok hdr)
    (N rem : Nat) (hlen : hb.length = keccakAbsorbStep * N + rem)
    (hrem : rem ≤ 135) :
    keccakBodyDigest hb N rem = EvmAsm.Stateless.SpecRef.headerHash hdr := by
  rw [keccakBodyDigest_eq_specref hb N rem hlen (by
    simp only [keccakAbsorbStep]; omega)]
  show EvmAsm.Stateless.SpecRef.keccak256 hb = _
  unfold EvmAsm.Stateless.SpecRef.headerHash
  rw [EvmAsm.Stateless.SpecRef.encode_headerToRlpItem_of_decode hdec]

/-! ### The composed whole-routine claim (#12223)

    `block_hash_from_header_spec_within` with its `input` instantiated at bytes
    the reference header decoder ACCEPTS. The post's digest cell then reads
    `SpecRef.headerHash hdr` rather than the guest's own `keccakBodyDigest`, and
    the only hypothesis added to the machine triple's resource/ABI bundle is the
    decode. Everything else in the post is unchanged — `keccakCallerPost` is
    unfolded in the statement precisely so the one substituted conjunct is
    visible rather than hidden behind a definition. -/

/-- ⭐⭐ **`block_hash_from_header` against the reference header hash.**

    `_decode_header hb = .ok hdr` ⇒ running the routine over `hb` leaves
    `SpecRef.headerHash hdr` in the 32-byte output cell.

    DOMAIN, honestly: everything except `hdec` is the resource/ABI bundle of
    `block_hash_from_header_spec_within` — return-address alignment, the
    `hb.length = 136 * N + rem` partition, sponge-scratch size/alignment/validity
    at `zk3_state`, and byte-access validity over the input window. Those are
    caller obligations, not input-domain gates. `hdec` IS an input-domain
    restriction, and it is the intended one: it is what makes the bytes a
    header at all.

    What this does NOT say: nothing here connects `hdec` to the guest's own
    `header_extended_decode` — see the module note above. -/
theorem block_hash_from_header_headerHash_within
    (sp0 ret inputBase outputBase : Word)
    (hb : List (BitVec 8)) (hdr : EvmAsm.Stateless.SpecRef.Header) (N rem : Nat)
    (v8 v9 v18 v20 v28 v29 : Word)
    (os : List (BitVec 8)) (A : Assertion) (hA : A.pcFree)
    (hdec : EvmAsm.Stateless.SpecRef._decode_header hb = .ok hdr)
    (halign_ret : (ret &&& ~~~(1 : Word)) = ret)
    (hlen : hb.length = keccakAbsorbStep * N + rem)
    (hrem_le : rem ≤ 135)
    (hos : os.length = 200)
    (halign_zk : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat % 8 = 0)
    (hover : (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + 200 < 2 ^ 64)
    (hNbound : keccakAbsorbStep * N + rem < 2 ^ 63)
    (hrem64 : rem < 2 ^ 64)
    (hb8i : (keccakAbsorbCursor inputBase N).toNat % 8 = 0)
    (hovers : ∀ n, n < rem →
      (BitVec.ofNat 64 GuestAddrs.zk3_state).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hoveri : ∀ n, n < rem →
      (keccakAbsorbCursor inputBase N).toNat + (rem - (n + 1)) < 2 ^ 64)
    (hvalids : ∀ n, n < rem →
      isValidByteAccess
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidi : ∀ n, n < rem →
      isValidByteAccess
        (keccakAbsorbCursor inputBase N + BitVec.ofNat 64 (rem - (n + 1))) = true)
    (hvalidRem : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 rem) = true)
    (hvalid135 : isValidByteAccess
      (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 135) = true)
    (hvalidMem : ∀ j, j < 200 →
      isValidMemAddr
        (BitVec.ofNat 64 GuestAddrs.zk3_state + BitVec.ofNat 64 j) = true) :
    cpsTripleWithin (6 + (5 + keccakBodyFuel N rem + 6)) B ret fullCode
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        memOwn (sp0 + signExtend12 (-16 : BitVec 12)) **
        stackFree (sp0 + signExtend12 (-16 : BitVec 12)) 4 **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        keccakCallerPre inputBase (BitVec.ofNat 64 hb.length) outputBase
          v28 v29 os hb (List.replicate 32 (0 : BitVec 8)) A)
      ((.x2 ↦ᵣ sp0) ** (.x1 ↦ᵣ ret) **
        ((sp0 + signExtend12 (-16 : BitVec 12)) ↦ₘ ret) **
        frameSlotsSaved keccakFrame
          (sp0 + signExtend12 (-16 : BitVec 12) +
            signExtend12 (-32 : BitVec 12))
          (keccakEntryVals v8 v9 v18 v20) **
        regsAt keccakFrame (keccakEntryVals v8 v9 v18 v20) **
        ((regOwn .x5) ** (.x10 ↦ᵣ (0 : Word)) **
          bytesRegion (BitVec.ofNat 64 GuestAddrs.zk3_state)
            (setBytes (keccakGuestPad (keccakBodyPrePad hb N rem) rem) 0
              (keccakBytes (keccakGuestPad (keccakBodyPrePad hb N rem) rem) 0)) **
          bytesRegion outputBase (EvmAsm.Stateless.SpecRef.headerHash hdr) **
          ((.x0 ↦ᵣ (0 : Word)) ** regOwns keccakCsrsRestNoX5 **
            keccakCallerFreeA inputBase hb N A))) := by
  have hdig := keccakBodyDigest_eq_headerHash_of_decode hdec N rem hlen hrem_le
  have hbase := block_hash_from_header_spec_within sp0 ret inputBase outputBase
    hb N rem v8 v9 v18 v20 v28 v29 os A hA halign_ret hlen hrem_le hos halign_zk
    hover hNbound hrem64 hb8i hovers hoveri hvalids hvalidi hvalidRem hvalid135
    hvalidMem
  simp only [keccakCallerPost, hdig] at hbase
  exact hbase

/-! ### Non-vacuity, against the Python-pinned oracle

    The strongest control available here: evaluate BOTH sides of the identity at a
    concrete header and check each against the digest `SpecRef/BlocksRlp.lean`
    already pins to the Python spec. The left side is the GUEST's sponge model,
    the right side is the reference — so these two `#guard`s witness that the
    bridge relates two things that independently agree with Python, rather than
    two spellings of the same definition. -/

private def bhTestHeader : EvmAsm.Stateless.SpecRef.Header :=
  { isCurrentFork := true, parentHash := List.replicate 32 0,
    ommersHash := List.replicate 32 0, coinbase := List.replicate 20 0,
    stateRoot := List.replicate 32 0, transactionsRoot := List.replicate 32 0,
    receiptRoot := List.replicate 32 0, bloom := List.replicate 256 0,
    difficulty := 0, number := 1, gasLimit := 30000000, gasUsed := 0,
    timestamp := 0, extraData := [], prevRandao := List.replicate 32 0,
    nonce := List.replicate 8 0, baseFeePerGas := 7,
    withdrawalsRoot := List.replicate 32 0, blobGasUsed := 0,
    excessBlobGas := 0, parentBeaconBlockRoot := List.replicate 32 0,
    requestsHash := List.replicate 32 0,
    blockAccessListHash := List.replicate 32 0, slotNumber := 1 }

private def bhTestBytes : List (BitVec 8) :=
  EvmAsm.EL.RLP.encode (EvmAsm.Stateless.SpecRef.headerToRlpItem bhTestHeader)

-- The encoded header is a real byte string, not an empty or degenerate one.
#guard bhTestBytes.length > 100

-- Reference side: matches the value pinned against the Python spec.
#guard EvmAsm.Stateless.SpecRef.bytesBEtoNat
    (EvmAsm.Stateless.SpecRef.headerHash bhTestHeader)
  == 0xaa1274562be0d8f34002861987fa166ee8903056f4df36509220bd9c7b8f89e2

-- Guest-model side: the same value, computed through `keccakBodyDigest`.
#guard EvmAsm.Stateless.SpecRef.bytesBEtoNat
    (keccakBodyDigest bhTestBytes (bhTestBytes.length / 136)
      (bhTestBytes.length % 136))
  == 0xaa1274562be0d8f34002861987fa166ee8903056f4df36509220bd9c7b8f89e2

/-! ### Non-vacuity of the COMPOSED claim

    The guards above are about the hash leg. The composition adds one hypothesis
    — `_decode_header hb = .ok hdr` — and a bundled hypothesis nothing satisfies
    would make `block_hash_from_header_headerHash_within` a statement about the
    empty set. Two directions, both checked. -/

/-! #### Satisfiable: the pinned header's encoding is on the accepting path -/

-- `hdec` HOLDS at `bhTestBytes`, so the composed theorem's hypothesis bundle is
-- inhabited (every other hypothesis is a resource/ABI fact the caller chooses).
#guard match EvmAsm.Stateless.SpecRef._decode_header bhTestBytes with
  | .ok _ => true
  | .error _ => false

-- ... and its conclusion, evaluated: the guest sponge model over the SUPPLIED
-- bytes equals the reference hash of the header the DECODER returns from them.
-- Combined with the two pinned guards above, both sides are also the value the
-- Python reference computes.
#guard match EvmAsm.Stateless.SpecRef._decode_header bhTestBytes with
  | .ok h => keccakBodyDigest bhTestBytes (bhTestBytes.length / 136)
      (bhTestBytes.length % 136) == EvmAsm.Stateless.SpecRef.headerHash h
  | .error _ => false

/-! #### Negative control: where `hdec` is FALSE, so is the conclusion

    `bhBadBytes` re-encodes the pinned header's field list with field 8
    (`number`, value 1) written as `[0x00, 0x01]` — the same value, one leading
    zero byte. That is well-formed RLP, and `decodeFully` accepts it, so a
    weaker hypothesis ("`hb` is well-formed RLP") would admit these bytes. The
    decoder's numeric-canonicality check (#11513) rejects them, and the digest
    of these bytes is NOT the pinned header hash — so on this input the
    conclusion is false and the theorem is right to make no claim. That is what
    makes `hdec` load-bearing rather than decorative. -/

private def bhBadItem : EvmAsm.EL.RLP.RLPItem :=
  match EvmAsm.Stateless.SpecRef.headerToRlpItem bhTestHeader with
  | .list items =>
      .list ((List.range items.length).map fun i =>
        if i = 8 then EvmAsm.EL.RLP.RLPItem.bytes [(0 : EvmAsm.EL.RLP.Byte), 1]
        else items.getD i (EvmAsm.EL.RLP.RLPItem.bytes []))
  | it => it

private def bhBadBytes : List (BitVec 8) := EvmAsm.EL.RLP.encode bhBadItem

-- Longer than, and genuinely different from, the canonical encoding: the
-- one-byte `0x01` scalar becomes the three-byte string `0x82 0x00 0x01`.
#guard bhBadBytes != bhTestBytes
#guard bhBadBytes.length > bhTestBytes.length

-- Well-formed RLP: the generic decoder accepts what the header decoder rejects.
#guard (EvmAsm.EL.RLP.decodeFully bhBadBytes).isSome
#guard match EvmAsm.Stateless.SpecRef._decode_header bhBadBytes with
  | .ok _ => false
  | .error _ => true

-- And the conclusion genuinely fails here: the digest of the non-canonical
-- bytes is not the pinned header hash.
#guard EvmAsm.Stateless.SpecRef.bytesBEtoNat
    (keccakBodyDigest bhBadBytes (bhBadBytes.length / 136)
      (bhBadBytes.length % 136))
  != 0xaa1274562be0d8f34002861987fa166ee8903056f4df36509220bd9c7b8f89e2


end EvmAsm.Codegen.BlockHashFromHeaderSpec
