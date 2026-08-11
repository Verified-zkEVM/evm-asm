/-
  EvmAsm.Codegen.Proofs.HashBridgeSha256Outer

  Phase-3 checkpoint for `zkvm_sha256`: the emitted outer countdown shell.
  The loop reloads x5 with the 64-byte stride, tests x18 with a signed BLT,
  runs the full-block body, and jumps back to the reload header.  The body is
  intentionally an explicit contract here; padding, digest/output, and the
  top-level SHA theorem remain later phases.
-/

import EvmAsm.Codegen.Proofs.HashBridgeSha256Block
import EvmAsm.Codegen.Proofs.HashBridgeKeccakSpec

namespace EvmAsm.Codegen.Proofs

open EvmAsm.Rv64
open EvmAsm.Rv64.SAsm
open EvmAsm.Codegen

set_option maxRecDepth 8000

private abbrev B : Word := BitVec.ofNat 64 GuestAddrs.zkvm_sha256
private abbrev sha256ProgL : List Instr := zkvmSha256_prog
private abbrev sha256Cr : CodeReq := CodeReq.ofProg B sha256ProgL

private abbrev sha256BlockStep : Nat := 64
private abbrev sha256OuterBodyFuel : Nat := 22
private abbrev sha256OuterExitOff : BitVec 13 := 92

private theorem sha256ProgL_len : sha256ProgL.length = 121 := by
  simp only [sha256ProgL, zkvmSha256_prog, zkvmSha256_prog_of]
  decide

private theorem sha256ProgL_bound : 4 * sha256ProgL.length < 2 ^ 64 := by
  rw [sha256ProgL_len]
  norm_num

private theorem mem_at (k : Nat) (ins : Instr) (A : Word)
    (hA : A = B + BitVec.ofNat 64 (4 * k))
    (hk : k < sha256ProgL.length)
    (hins : sha256ProgL[k]'hk = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i → sha256Cr a = some i :=
  fun a i h => CodeReq.ofProg_mem_at B A sha256ProgL k ins hA hk hins
    sha256ProgL_bound a i h

private theorem outer_li_mem : ∀ a i,
    CodeReq.singleton (B + 100) (.LI .x5 (BitVec.ofNat 64 sha256BlockStep)) a = some i →
      sha256Cr a = some i := by
  intro a i h
  exact mem_at 25 (.LI .x5 (BitVec.ofNat 64 sha256BlockStep)) (B + 100) (by decide)
    (by rw [sha256ProgL_len]; decide) (by rfl) a i h

private theorem outer_guard_mem : ∀ a i,
    CodeReq.singleton (B + 104) (.BLT .x18 .x5 sha256OuterExitOff) a = some i →
      sha256Cr a = some i := by
  intro a i h
  have hmem := mem_at 26 (.BLT .x18 .x5 sha256OuterExitOff) (B + 104)
    (by decide) (by rw [sha256ProgL_len]; decide) (by rfl)
  exact hmem a i h

private theorem outer_exit_addr :
    (B + 104 : Word) + signExtend13 sha256OuterExitOff = B + 196 := by
  decide

/-- The emitted SHA-256 outer loop, without claiming the meaning of its body.

    The loop header is `LI x5,64` at `B+100`, followed by `BLT x18,x5,+92`
    at `B+104`; a 22-step body starts at `B+108` and returns to `B+100`.
    The body post deliberately gives x5 back as `regOwn`, because the header
    reload is the ownership boundary.  Padding, digest/output, and the
    top-level `zkvm_sha256_spec_within` are outside this checkpoint. -/
theorem sha256FullBlockLoop_reload_spec
    (N rem : Nat) (inv : Nat → Assertion) (_hpcFree : ∀ n, (inv n).pcFree)
    (hrem : rem < sha256BlockStep)
    (hNbound : sha256BlockStep * N + rem < 2 ^ 63)
    (hbody : ∀ n, n < N →
      cpsTripleWithin sha256OuterBodyFuel (B + 108) (B + 100) sha256Cr
        ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** inv (n + 1))
        ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
          (regOwn .x5) ** inv n)) :
    cpsTripleWithin (N * (sha256OuterBodyFuel + 2) + 2) (B + 100) (B + 196) sha256Cr
      ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * N + rem)) **
        (regOwn .x5) ** inv N)
      ((.x18 ↦ᵣ BitVec.ofNat 64 rem) **
        (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** inv 0) := by
  have hstepbound : sha256BlockStep < 2 ^ 63 := by
    simp only [sha256BlockStep]
    omega
  have hbody' : ∀ n, n < N →
      cpsTripleWithin sha256OuterBodyFuel ((B + 100) + 8) (B + 100) sha256Cr
        ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * (n + 1) + rem)) **
          (.x5 ↦ᵣ BitVec.ofNat 64 sha256BlockStep) ** inv (n + 1))
        ((.x18 ↦ᵣ BitVec.ofNat 64 (sha256BlockStep * n + rem)) **
          (regOwn .x5) ** inv n) := by
    intro n hn
    simpa only [show (B + 100 : Word) + 8 = B + 108 by decide] using hbody n hn
  exact signedCountdownLoop_reload_spec sha256Cr (B + 100) (B + 196) .x18 .x5
    sha256OuterExitOff sha256OuterBodyFuel sha256BlockStep N rem inv
    (by decide) (by decide) (by decide) hrem hstepbound hNbound
    outer_exit_addr (fun n => _hpcFree n) outer_li_mem outer_guard_mem hbody'

end EvmAsm.Codegen.Proofs
