/-
  EvmAsm.Codegen.Programs.MessageCallGasSAsm

  `message_call_gas` via the **multi-register shared return-tail**
  (`EvmAsm/Rv64/SAsm/MultiRegRetTail.lean`, bead evm-asm-24uka) — the
  acceptance consumer.

  The routine (EIP-150 CALL gas forwarding, mirroring execution-specs
  Amsterdam `calculate_message_call_gas` / `max_message_call_gas`) is a
  straight-line forward join with THREE return tails:

  ```
        mv   t0,a0 ; mv t1,a1 ; mv t2,a2 ; mv t3,a3 ; mv t4,a4
        add  t5, t3, t4                -- s = memory_cost + extra_gas
        bltu t5, t3, .err1             -- input sum overflow → status 1
        li   t6, 0
        beq  t0, x0, .nostip
        lui  t6, 1 ; addiw t6, t6, -1796   -- stipend = 2300
  .nostip:
        bltu t2, t5, .insuf
        sub  a5, t2, t5 ; srli a6, a5, 6 ; sub a6, a5, a6
        mv   a3, t1 ; bgeu a6, t1, .cap ; mv a3, a6 ; j .cap
  .insuf: mv a3, t1
  .cap: add a1, a3, t4 ; bltu a1, a3, .err2       -- jumps OVER two tails
        add a2, a3, t6 ; bltu a2, a3, .err2       -- jumps OVER two tails
        li a0, 0 ; ret                            -- success tail
  .err1: li a0, 1 ; li a1, 0 ; li a2, 0 ; li a3, 0 ; ret
  .err2: li a0, 2 ; li a1, 0 ; li a2, 0 ; li a3, 0 ; ret
  ```

  The two error tails are `multiRegRetTail_spec` instances (four
  registers each, proven once per tail address); the two output-overflow
  guards exercise **branch-over-tail**: they route to the `.err2` tail at
  `base+124`, jumping over the success (`base+96`) and `.err1`
  (`base+104`) tails — the stations are target-address-agnostic, the
  skipped tails' bytes stay in the routine's single `CodeReq`.

  **Genuine post** (`messageCallGas_spec`): the full status/gas semantics
  — `a0 = 1` on input-sum overflow, else `a0 = 2` when `capped + extra`
  or `capped + stipend` overflows, else `a0 = 0` with `a1 = capped +
  extra_gas` (caller charge), `a2 = capped + stipend` (child gas),
  `a3 = capped` — where `capped` is the EIP-150 all-but-one-64th cap and
  `stipend` the 2300 value-transfer stipend (`stipend`/`capped`/`mcgPost`
  below).  The error tails pin `a1 = a2 = a3 = 0`.

  `message_call_gas` is not linked into the main guest image (it is a
  probe/registry routine — no `GuestAddrs` anchor), so the spec is stated
  at a SYMBOLIC base over the emitted `messageCallGas_prog` directly:
  byte-transparent (no byte change, no A/B), and consumable at whatever
  address a closure links it.
-/

import EvmAsm.Codegen.Programs.EvmMessageCallGas
import EvmAsm.Rv64.SAsm.MultiRegRetTail
import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Codegen

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm

namespace MessageCallGasSAsm

/-! ## The routine's semantics -/

/-- The EIP-150 call stipend: `2300` on value-bearing calls, else `0`. -/
def stipend (v : Word) : Word := if v = 0 then 0 else 2300

/-- The EIP-150 gas cap: with `s = memory_cost + extra_gas`, an
    insufficient frame (`gas_left < s`) forwards the raw request;
    otherwise the request is capped at all-but-one-64th of the remaining
    gas. -/
def capped (r g s : Word) : Word :=
  if BitVec.ult g s then r
  else if BitVec.ult ((g - s) - ((g - s) >>> 6)) r
    then (g - s) - ((g - s) >>> 6) else r

/-- The four output registers `a0..a3`. -/
def mcgOut (a0v a1v a2v a3v : Word) : Assertion :=
  ((.x10 : Reg) ↦ᵣ a0v) ** ((.x11 : Reg) ↦ᵣ a1v) **
  ((.x12 : Reg) ↦ᵣ a2v) ** ((.x13 : Reg) ↦ᵣ a3v)

/-- The genuine outcome: status 1 on input-sum overflow, status 2 when
    `capped + extra` or `capped + stipend` overflows, else success with
    the computed charge / child gas / capped request. -/
def mcgPost (v r g m e : Word) : Assertion :=
  if BitVec.ult (m + e) m then mcgOut 1 0 0 0
  else if BitVec.ult (capped r g (m + e) + e) (capped r g (m + e)) then
    mcgOut 2 0 0 0
  else if BitVec.ult (capped r g (m + e) + stipend v) (capped r g (m + e))
    then mcgOut 2 0 0 0
  else mcgOut 0 (capped r g (m + e) + e) (capped r g (m + e) + stipend v)
    (capped r g (m + e))

/-! ## Code-membership helpers (symbolic base) -/

/-- `messageCallGas_prog` exposed at `List Instr` (the `Program` alias is
    a plain `def`, opaque to `GetElem` instance search). -/
private def mcgProg : List Instr := messageCallGas_prog

private theorem mcgProg_eq : mcgProg = messageCallGas_prog := rfl

private theorem mcg_mem (base A : Word) (k : Nat) (ins : Instr)
    (hA : A = base + BitVec.ofNat 64 (4 * k)) (hk : k < 36)
    (hins : ∀ h : k < mcgProg.length, mcgProg[k]'h = ins) :
    ∀ a i, CodeReq.singleton A ins a = some i →
      CodeReq.ofProg base messageCallGas_prog a = some i := by
  have hk' : k < mcgProg.length := by
    rw [show mcgProg.length = 36 from rfl]
    exact hk
  have h := CodeReq.ofProg_mem_at base A mcgProg k ins hA hk' (hins hk')
    (by decide)
  rwa [mcgProg_eq] at h

private theorem mcg_mem_err1 (base : Word) : ∀ a i,
    CodeReq.ofProg (base + 104)
      (liRetTailProg [(.x10, (1 : Word)), (.x11, 0), (.x12, 0), (.x13, 0)])
      a = some i →
    CodeReq.ofProg base messageCallGas_prog a = some i :=
  CodeReq.ofProg_mono_sub base (base + 104) _ _ 26 rfl rfl (by decide)
    (by decide)

private theorem mcg_mem_err2 (base : Word) : ∀ a i,
    CodeReq.ofProg (base + 124)
      (liRetTailProg [(.x10, (2 : Word)), (.x11, 0), (.x12, 0), (.x13, 0)])
      a = some i →
    CodeReq.ofProg base messageCallGas_prog a = some i :=
  CodeReq.ofProg_mono_sub base (base + 124) _ _ 31 rfl rfl (by decide)
    (by decide)

/-! ## The error tails (multi-register shared return tails) -/

/-- An error tail `li a0, status ; li a1, 0 ; li a2, 0 ; li a3, 0 ; ret`
    at `addr`, instantiated from `multiRegRetTail_spec` with an arbitrary
    pcFree frame: the four output registers are pinned (whatever they
    held), everything framed is untouched. -/
private theorem errTail_spec (cr : CodeReq) (addr ret status : Word)
    (w10 w11 w12 w13 : Word) (F : Assertion) (hF : F.pcFree)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hmem : ∀ a i, CodeReq.ofProg addr
      (liRetTailProg [(.x10, status), (.x11, 0), (.x12, 0), (.x13, 0)])
      a = some i → cr a = some i) :
    cpsTripleWithin 5 addr ret cr
      (((.x10 : Reg) ↦ᵣ w10) ** ((.x11 : Reg) ↦ᵣ w11) **
        ((.x12 : Reg) ↦ᵣ w12) ** ((.x13 : Reg) ↦ᵣ w13) **
        ((.x1 : Reg) ↦ᵣ ret) ** F)
      (((.x10 : Reg) ↦ᵣ status) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
        ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ (0 : Word)) **
        ((.x1 : Reg) ↦ᵣ ret) ** F) := by
  have hcore := multiRegRetTail_spec cr addr ret
    [(.x10, status), (.x11, 0), (.x12, 0), (.x13, 0)]
    (by rintro rc hrc; fin_cases hrc <;> exact fun hx => Reg.noConfusion hx)
    (by simp only [List.length_cons, List.length_nil]; omega)
    halignRet hmem
  have hcoreF := cpsTripleWithin_frameR F hF hcore
  refine cpsTripleWithin_weaken (fun h hp => ?_) (fun h hq => ?_) hcoreF
  · have hp1 : (((.x10 : Reg) ↦ᵣ w10) ** (((.x11 : Reg) ↦ᵣ w11) **
        (((.x12 : Reg) ↦ᵣ w12) ** (((.x13 : Reg) ↦ᵣ w13) **
          (((.x1 : Reg) ↦ᵣ ret) ** F))))) h := by
      xperm_hyp hp
    have hp2 := sepConj_mono (regIs_to_regOwn .x10 _)
      (sepConj_mono (regIs_to_regOwn .x11 _)
        (sepConj_mono (regIs_to_regOwn .x12 _)
          (sepConj_mono (regIs_to_regOwn .x13 _)
            (fun _ hh => hh)))) h hp1
    simp only [List.map_cons, List.map_nil, regOwns_cons, regOwns_nil,
      sepConj_emp_right']
    xperm_hyp hp2
  · simp only [regsSet_cons, regsSet_nil, sepConj_emp_right'] at hq
    xperm_hyp hq

/-! ## The whole-routine post -/

/-- `mcgPost` plus the untouched input/frame registers: `a4` preserved,
    all scratch registers merely owned. -/
def mcgFullPost (v r g m e ret : Word) : Assertion :=
  mcgPost v r g m e ** ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
  ((.x0 : Reg) ↦ᵣ (0 : Word)) **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 **
  regOwn .x30 ** regOwn .x31 ** regOwn .x15 ** regOwn .x16

/-! ## The shared suffix from the `.cap` join (base+80) -/

/-- From the `.cap` join with `a3 = capped`: compute `cost`/`sub_call`,
    the two output-overflow guards routing (over the success and
    `status-1` tails) to the `status-2` tail, else the success tail. -/
private theorem from80_spec (base ret v r g m e : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hnOver : ¬ BitVec.ult (m + e) m) :
    cpsTripleWithin 9 (base + 80) ret
      (CodeReq.ofProg base messageCallGas_prog)
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x13 : Reg) ↦ᵣ capped r g (m + e)) ** ((.x14 : Reg) ↦ᵣ e) **
        ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (mcgFullPost v r g m e ret) := by
  set CR := CodeReq.ofProg base messageCallGas_prog with hCR
  -- add a1, a3, t4  (cost = capped + extra)
  have hadd11 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 80) 20 _ rfl (by omega) (fun _ => rfl))
    (h := add_spec_gen_within .x11 .x13 .x29 (capped r g (m + e)) e r
      (base + 80) (by decide))
  rw [show (base + 80) + 4 = base + 84 from by
    rw [BitVec.add_assoc, show ((80 : Word) + 4) = (84 : Word) from by decide]]
    at hadd11
  -- bltu a1, a3, .err2  (jumps OVER the success and status-1 tails)
  have hbr21 := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x12 : Reg) ↦ᵣ g) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      regOwn .x15 ** regOwn .x16 **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 84) 21 _ rfl (by omega) (fun _ => rfl))
      (h := bltu_spec_gen_within .x11 .x13 (40 : BitVec 13)
        (capped r g (m + e) + e) (capped r g (m + e)) (base + 84)))
  rw [show (base + 84) + signExtend13 (40 : BitVec 13) = base + 124 from by
        rw [BitVec.add_assoc,
          show ((84 : Word) + signExtend13 (40 : BitVec 13)) = (124 : Word)
            from by decide],
      show (base + 84) + 4 = base + 88 from by
        rw [BitVec.add_assoc,
          show ((84 : Word) + (4 : Word)) = (88 : Word) from by decide]]
    at hbr21
  -- the status-2 tail, consumed by BOTH overflow stations
  -- (arm of station 21: x12 still holds g)
  have htail21 : BitVec.ult (capped r g (m + e) + e) (capped r g (m + e)) →
      cpsTripleWithin 7 (base + 124) ret CR
        (((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
          ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          regOwn .x15 ** regOwn .x16 **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (mcgFullPost v r g m e ret) := by
    intro h21
    have h := errTail_spec CR (base + 124) ret (2 : Word) v
      (capped r g (m + e) + e) g (capped r g (m + e))
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) halignRet (by rw [hCR]; exact mcg_mem_err2 base)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => ?_) h)
    unfold mcgFullPost mcgPost
    rw [if_neg hnOver, if_pos h21]
    unfold mcgOut
    have hq1 : (((.x5 : Reg) ↦ᵣ v) ** (((.x6 : Reg) ↦ᵣ r) **
        (((.x7 : Reg) ↦ᵣ g) ** (((.x28 : Reg) ↦ᵣ m) **
          (((.x29 : Reg) ↦ᵣ e) ** (((.x30 : Reg) ↦ᵣ (m + e)) **
            (((.x31 : Reg) ↦ᵣ stipend v) **
              (((.x10 : Reg) ↦ᵣ (2 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
               ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ (0 : Word)) **
               ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
               ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x15 ** regOwn .x16)))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (sepConj_mono (regIs_to_regOwn .x31 _)
                  (fun _ hh => hh))))))) h hq1
    xperm_hyp hq2
  -- fall of station 21: add a2, a3, t6 (sub_call = capped + stipend)
  have hadd12 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 88) 22 _ rfl (by omega) (fun _ => rfl))
    (h := add_spec_gen_within .x12 .x13 .x31 (capped r g (m + e)) (stipend v)
      g (base + 88) (by decide))
  rw [show (base + 88) + 4 = base + 92 from by
    rw [BitVec.add_assoc, show ((88 : Word) + 4) = (92 : Word) from by decide]]
    at hadd12
  -- bltu a2, a3, .err2  (jumps OVER the success and status-1 tails)
  have hbr23 := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
      ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      regOwn .x15 ** regOwn .x16 **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 92) 23 _ rfl (by omega) (fun _ => rfl))
      (h := bltu_spec_gen_within .x12 .x13 (32 : BitVec 13)
        (capped r g (m + e) + stipend v) (capped r g (m + e)) (base + 92)))
  rw [show (base + 92) + signExtend13 (32 : BitVec 13) = base + 124 from by
        rw [BitVec.add_assoc,
          show ((92 : Word) + signExtend13 (32 : BitVec 13)) = (124 : Word)
            from by decide],
      show (base + 92) + 4 = base + 96 from by
        rw [BitVec.add_assoc,
          show ((92 : Word) + (4 : Word)) = (96 : Word) from by decide]]
    at hbr23
  -- the status-2 tail again (arm of station 23: x12 holds sub_call)
  have htail23 : ¬ BitVec.ult (capped r g (m + e) + e) (capped r g (m + e)) →
      BitVec.ult (capped r g (m + e) + stipend v) (capped r g (m + e)) →
      cpsTripleWithin 5 (base + 124) ret CR
        (((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
          ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
          ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
          ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          regOwn .x15 ** regOwn .x16 **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (mcgFullPost v r g m e ret) := by
    intro h21n h23
    have h := errTail_spec CR (base + 124) ret (2 : Word) v
      (capped r g (m + e) + e) (capped r g (m + e) + stipend v)
      (capped r g (m + e))
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) halignRet (by rw [hCR]; exact mcg_mem_err2 base)
    refine cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
      (fun h hq => ?_) h
    unfold mcgFullPost mcgPost
    rw [if_neg hnOver, if_neg h21n, if_pos h23]
    unfold mcgOut
    have hq1 : (((.x5 : Reg) ↦ᵣ v) ** (((.x6 : Reg) ↦ᵣ r) **
        (((.x7 : Reg) ↦ᵣ g) ** (((.x28 : Reg) ↦ᵣ m) **
          (((.x29 : Reg) ↦ᵣ e) ** (((.x30 : Reg) ↦ᵣ (m + e)) **
            (((.x31 : Reg) ↦ᵣ stipend v) **
              (((.x10 : Reg) ↦ᵣ (2 : Word)) ** ((.x11 : Reg) ↦ᵣ (0 : Word)) **
               ((.x12 : Reg) ↦ᵣ (0 : Word)) ** ((.x13 : Reg) ↦ᵣ (0 : Word)) **
               ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
               ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x15 ** regOwn .x16)))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (sepConj_mono (regIs_to_regOwn .x31 _)
                  (fun _ hh => hh))))))) h hq1
    xperm_hyp hq2
  -- the success tail: li a0, 0 ; ret
  have hsucc : ¬ BitVec.ult (capped r g (m + e) + e) (capped r g (m + e)) →
      ¬ BitVec.ult (capped r g (m + e) + stipend v) (capped r g (m + e)) →
      cpsTripleWithin 5 (base + 96) ret CR
        (((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
          ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
          ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
          ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          regOwn .x15 ** regOwn .x16 **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (mcgFullPost v r g m e ret) := by
    intro h21n h23n
    have hli := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 96) 24 _ rfl (by omega) (fun _ => rfl))
      (h := li_spec_gen_within .x10 v (0 : Word) (base + 96) (by decide))
    rw [show (base + 96) + 4 = base + 100 from by
      rw [BitVec.add_assoc,
        show ((96 : Word) + 4) = (100 : Word) from by decide]] at hli
    have hret := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 100) 25 _ rfl (by omega) (fun _ => rfl))
      (h := EvmAsm.Evm64.ret_spec_within' (base + 100) ret)
    rw [halignRet] at hret
    have hliF := cpsTripleWithin_frameR
      (((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
        ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
        ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
        ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hli
    have hretF := cpsTripleWithin_frameR
      (((.x10 : Reg) ↦ᵣ (0 : Word)) **
        ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
        ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
        ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
        ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hret
    have hc := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hliF hretF
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => ?_) hc)
    unfold mcgFullPost mcgPost
    rw [if_neg hnOver, if_neg h21n, if_neg h23n]
    unfold mcgOut
    have hq1 : (((.x5 : Reg) ↦ᵣ v) ** (((.x6 : Reg) ↦ᵣ r) **
        (((.x7 : Reg) ↦ᵣ g) ** (((.x28 : Reg) ↦ᵣ m) **
          (((.x29 : Reg) ↦ᵣ e) ** (((.x30 : Reg) ↦ᵣ (m + e)) **
            (((.x31 : Reg) ↦ᵣ stipend v) **
              (((.x10 : Reg) ↦ᵣ (0 : Word)) **
               ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
               ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
               ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
               ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
               ((.x0 : Reg) ↦ᵣ (0 : Word)) **
               regOwn .x15 ** regOwn .x16)))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (sepConj_mono (regIs_to_regOwn .x31 _)
                  (fun _ hh => hh))))))) h hq1
    xperm_hyp hq2
  -- assemble: fall of station 21 = add ; station 23
  have hfall21 : ¬ BitVec.ult (capped r g (m + e) + e) (capped r g (m + e)) →
      cpsTripleWithin 7 (base + 88) ret CR
        (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) **
          ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          regOwn .x15 ** regOwn .x16 **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (mcgFullPost v r g m e ret) := by
    intro h21n
    have hadd12F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) **
        ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) **
        regOwn .x15 ** regOwn .x16 **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hadd12
    have hstation := retJoinStation_spec
      (cond := BitVec.ult (capped r g (m + e) + stipend v)
        (capped r g (m + e)))
      (PT := ((.x10 : Reg) ↦ᵣ v) **
        ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
        ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
        ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
        ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (PF := ((.x10 : Reg) ↦ᵣ v) **
        ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
        ((.x12 : Reg) ↦ᵣ (capped r g (m + e) + stipend v)) **
        ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
        ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        regOwn .x15 ** regOwn .x16 **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      hbr23
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun h23 => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (htail23 h21n h23))
      (fun h23n => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) (hsucc h21n h23n))
    exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq)
      (cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hadd12F hstation)
  -- station 21 wraps
  have hstation21 := retJoinStation_spec
    (cond := BitVec.ult (capped r g (m + e) + e) (capped r g (m + e)))
    (PT := ((.x10 : Reg) ↦ᵣ v) **
      ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
      ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
      ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      regOwn .x15 ** regOwn .x16 **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (PF := ((.x10 : Reg) ↦ᵣ v) **
      ((.x11 : Reg) ↦ᵣ (capped r g (m + e) + e)) **
      ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ capped r g (m + e)) **
      ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      regOwn .x15 ** regOwn .x16 **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    hbr21
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by xperm_hyp hq)
    (fun h21 => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (htail21 h21))
    (fun h21n => cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) (hfall21 h21n))
  -- add ; station 21
  have hadd11F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x12 : Reg) ↦ᵣ g) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
      ((.x31 : Reg) ↦ᵣ stipend v) **
      regOwn .x15 ** regOwn .x16 **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hadd11
  have hcomp := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hadd11F hstation21
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hcomp)

/-! ## The capping else-branch (base+48) -/

/-- The sufficient-gas branch: compute `max = avail - avail/64`, select
    `min requested max`, and continue at the `.cap` join. -/
private theorem elsePath_spec (base ret v r g m e w15 w16 : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret)
    (hnOver : ¬ BitVec.ult (m + e) m)
    (hnIns : ¬ BitVec.ult g (m + e)) :
    cpsTripleWithin 16 (base + 48) ret
      (CodeReq.ofProg base messageCallGas_prog)
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
        ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        ((.x15 : Reg) ↦ᵣ w15) ** ((.x16 : Reg) ↦ᵣ w16) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (mcgFullPost v r g m e ret) := by
  set CR := CodeReq.ofProg base messageCallGas_prog with hCR
  -- sub a5, t2, t5  (avail = gas_left - s)
  have hsub15 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 48) 12 _ rfl (by omega) (fun _ => rfl))
    (h := sub_spec_gen_within .x15 .x7 .x30 g (m + e) w15 (base + 48)
      (by decide))
  rw [show (base + 48) + 4 = base + 52 from by
    rw [BitVec.add_assoc, show ((48 : Word) + 4) = (52 : Word) from by decide]]
    at hsub15
  -- srli a6, a5, 6
  have hsrli := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 52) 13 _ rfl (by omega) (fun _ => rfl))
    (h := srli_spec_gen_within .x16 .x15 w16 (g - (m + e)) (6 : BitVec 6)
      (base + 52) (by decide))
  rw [show ((6 : BitVec 6)).toNat = 6 from rfl,
      show (base + 52) + 4 = base + 56 from by
        rw [BitVec.add_assoc,
          show ((52 : Word) + 4) = (56 : Word) from by decide]] at hsrli
  -- sub a6, a5, a6  (max = avail - avail/64)
  have hsub16 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 56) 14 _ rfl (by omega) (fun _ => rfl))
    (h := sub_spec_gen_rd_eq_rs2_within .x16 .x15 (g - (m + e))
      ((g - (m + e)) >>> 6) (base + 56) (by decide))
  rw [show (base + 56) + 4 = base + 60 from by
    rw [BitVec.add_assoc, show ((56 : Word) + 4) = (60 : Word) from by decide]]
    at hsub16
  -- mv a3, t1  (capped := requested)
  have hmv13 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 60) 15 _ rfl (by omega) (fun _ => rfl))
    (h := mv_spec_gen_within .x13 .x6 r m (base + 60) (by decide))
  rw [show (base + 60) + 4 = base + 64 from by
    rw [BitVec.add_assoc, show ((60 : Word) + 4) = (64 : Word) from by decide]]
    at hmv13
  -- bgeu a6, t1, .cap
  have hbr16 := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ r) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 64) 16 _ rfl (by omega) (fun _ => rfl))
      (h := bgeu_spec_gen_within .x16 .x6 (16 : BitVec 13)
        ((g - (m + e)) - ((g - (m + e)) >>> 6)) r (base + 64)))
  rw [show (base + 64) + signExtend13 (16 : BitVec 13) = base + 80 from by
        rw [BitVec.add_assoc,
          show ((64 : Word) + signExtend13 (16 : BitVec 13)) = (80 : Word)
            from by decide],
      show (base + 64) + 4 = base + 68 from by
        rw [BitVec.add_assoc,
          show ((64 : Word) + (4 : Word)) = (68 : Word) from by decide]]
    at hbr16
  -- taken arm: keep capped = requested
  have htaken16 : ¬ BitVec.ult ((g - (m + e)) - ((g - (m + e)) >>> 6)) r →
      cpsTripleWithin 11 (base + 80) ret CR
        (((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
          ((.x6 : Reg) ↦ᵣ r) **
          ((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
          ((.x13 : Reg) ↦ᵣ r) ** ((.x14 : Reg) ↦ᵣ e) **
          ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (mcgFullPost v r g m e ret) := by
    intro hMXn
    have hcap : capped r g (m + e) = r := by
      unfold capped
      rw [if_neg hnIns, if_neg hMXn]
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => ?_) (fun _ hq => hq)
        (from80_spec base ret v r g m e halignRet hnOver))
    rw [hcap]
    have hp1 : (((.x15 : Reg) ↦ᵣ (g - (m + e))) **
        ((((.x16 : Reg)) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
          (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
           ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
           ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ r) **
           ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
           ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
           ((.x31 : Reg) ↦ᵣ stipend v) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))) h := by
      xperm_hyp hp
    have hp2 := sepConj_mono (regIs_to_regOwn .x15 _)
      (sepConj_mono (regIs_to_regOwn .x16 _)
        (fun _ hh => hh)) h hp1
    xperm_hyp hp2
  -- fall arm: capped = max, then jump to the .cap join
  have hfall16 : BitVec.ult ((g - (m + e)) - ((g - (m + e)) >>> 6)) r →
      cpsTripleWithin 11 (base + 68) ret CR
        (((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
          ((.x6 : Reg) ↦ᵣ r) **
          ((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
          ((.x13 : Reg) ↦ᵣ r) ** ((.x14 : Reg) ↦ᵣ e) **
          ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (mcgFullPost v r g m e ret) := by
    intro hMX
    have hcap : capped r g (m + e)
        = (g - (m + e)) - ((g - (m + e)) >>> 6) := by
      unfold capped
      rw [if_neg hnIns, if_pos hMX]
    -- mv a3, a6
    have hmv := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 68) 17 _ rfl (by omega) (fun _ => rfl))
      (h := mv_spec_gen_within .x13 .x16
        ((g - (m + e)) - ((g - (m + e)) >>> 6)) r (base + 68) (by decide))
    rw [show (base + 68) + 4 = base + 72 from by
      rw [BitVec.add_assoc,
        show ((68 : Word) + 4) = (72 : Word) from by decide]] at hmv
    -- j .cap
    have hjal := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 72) 18 _ rfl (by omega) (fun _ => rfl))
      (h := jal_x0_spec_gen_within (8 : BitVec 21) (base + 72))
    rw [show (base + 72) + signExtend21 (8 : BitVec 21) = base + 80 from by
      rw [BitVec.add_assoc,
        show ((72 : Word) + signExtend21 (8 : BitVec 21)) = (80 : Word)
          from by decide]] at hjal
    have hmvF := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hmv
    have hjalF := cpsTripleWithin_frameR
      (((.x13 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
        ((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
        ((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
        ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hjal
    have hc1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        rw [sepConj_emp_left']
        xperm_hyp hp) hmvF hjalF
    have hfrom80 := from80_spec base ret v r g m e halignRet hnOver
    have hc2 := cpsTripleWithin_seq_perm_same_cr
      (fun h hp => by
        rw [sepConj_emp_left'] at hp
        rw [hcap]
        have hp1 : (((.x15 : Reg) ↦ᵣ (g - (m + e))) **
            ((((.x16 : Reg)) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
              (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
               ((.x7 : Reg) ↦ᵣ g) ** ((.x10 : Reg) ↦ᵣ v) **
               ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
               ((.x13 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
               ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
               ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
               ((.x31 : Reg) ↦ᵣ stipend v) **
               ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))) h := by
          xperm_hyp hp
        have hp2 := sepConj_mono (regIs_to_regOwn .x15 _)
          (sepConj_mono (regIs_to_regOwn .x16 _)
            (fun _ hh => hh)) h hp1
        xperm_hyp hp2) hc1 hfrom80
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hc2)
  -- the min-select station
  have hstation16 := retJoinStation_spec
    (cond := ¬ BitVec.ult ((g - (m + e)) - ((g - (m + e)) >>> 6)) r)
    (PT := ((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
      ((.x6 : Reg) ↦ᵣ r) **
      ((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ r) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (PF := ((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
      ((.x6 : Reg) ↦ᵣ r) **
      ((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ r) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    hbr16
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by
      have hq1 : (⌜BitVec.ult ((g - (m + e)) - ((g - (m + e)) >>> 6)) r⌝ **
          (((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
           ((.x6 : Reg) ↦ᵣ r) **
           ((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
           ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
           ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ r) **
           ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
           ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
           ((.x31 : Reg) ↦ᵣ stipend v) **
           ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
           ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))) h := by
        xperm_hyp hq
      obtain ⟨hMX, hrest⟩ := (sepConj_pure_left h).1 hq1
      exact (sepConj_pure_left h).2 ⟨fun hn => hn hMX, hrest⟩)
    (fun hMXn => htaken16 hMXn)
    (fun hMXnn => hfall16 (not_not.mp hMXnn))
  -- assemble the prefix
  have hsub15F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x31 : Reg) ↦ᵣ stipend v) ** ((.x16 : Reg) ↦ᵣ w16) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsub15
  have hsrliF := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsrli
  have hsub16F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hsub16
  have hmv13F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
      ((.x15 : Reg) ↦ᵣ (g - (m + e))) **
      ((.x16 : Reg) ↦ᵣ ((g - (m + e)) - ((g - (m + e)) >>> 6))) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf) hmv13
  have hc1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hsub15F hsrliF
  have hc2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc1 hsub16F
  have hc3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc2 hmv13F
  have hc4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hc3 hstation16
  exact cpsTripleWithin_mono_nSteps (by omega)
    (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
      (fun _ hq => hq) hc4)

/-! ## The whole routine -/

/-- **`message_call_gas` at a symbolic base** (genuine post): the full
    EIP-150 status/gas outcome (`mcgPost`) — `a0 = 1` on input-sum
    overflow with `a1 = a2 = a3 = 0`, `a0 = 2` when `capped + extra_gas`
    or `capped + stipend` overflows (also zeroing `a1..a3`), else
    `a0 = 0` with `a1 = capped + extra_gas`, `a2 = capped + stipend`,
    `a3 = capped`; the `a4` input preserved.  Stated over the emitted
    `messageCallGas_prog` (byte-transparent; the routine has no
    `GuestAddrs` anchor — probe closures link it wherever). -/
theorem messageCallGas_spec (base ret v r g m e : Word)
    (halignRet : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 28 base ret (CodeReq.ofProg base messageCallGas_prog)
      (((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
        regOwn .x5 ** regOwn .x6 ** regOwn .x7 ** regOwn .x28 **
        regOwn .x29 ** regOwn .x30 ** regOwn .x31 **
        regOwn .x15 ** regOwn .x16)
      (mcgFullPost v r g m e ret) := by
  set CR := CodeReq.ofProg base messageCallGas_prog with hCR
  -- peel the scratch registers
  refine cpsTripleWithin_weaken
    (fun h hp => by
      simp only [regOwns_cons, regOwns_nil, sepConj_emp_right']
      xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_peel_regOwns
      [.x5, .x6, .x7, .x28, .x29, .x30, .x31, .x15, .x16] (by decide)
      (P := ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
        ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (fun vf => ?_))
  simp only [regAtomsOf_cons, regAtomsOf_nil, sepConj_emp_right']
  -- ---- init: 5 MVs + ADD ----
  have hmv5 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base base 0 _ (by
        rw [show (4 : Nat) * 0 = 0 from rfl]
        rw [show (BitVec.ofNat 64 0 : Word) = (0 : Word) from rfl]
        bv_omega) (by omega) (fun _ => rfl))
    (h := mv_spec_gen_within .x5 .x10 v (vf .x5) base (by decide))
  rw [show base + 4 = base + 4 from rfl] at hmv5
  have hmv6 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 4) 1 _ rfl (by omega) (fun _ => rfl))
    (h := mv_spec_gen_within .x6 .x11 r (vf .x6) (base + 4) (by decide))
  rw [show (base + 4) + 4 = base + 8 from by
    rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]]
    at hmv6
  have hmv7 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 8) 2 _ rfl (by omega) (fun _ => rfl))
    (h := mv_spec_gen_within .x7 .x12 g (vf .x7) (base + 8) (by decide))
  rw [show (base + 8) + 4 = base + 12 from by
    rw [BitVec.add_assoc, show ((8 : Word) + 4) = (12 : Word) from by decide]]
    at hmv7
  have hmv28 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 12) 3 _ rfl (by omega) (fun _ => rfl))
    (h := mv_spec_gen_within .x28 .x13 m (vf .x28) (base + 12) (by decide))
  rw [show (base + 12) + 4 = base + 16 from by
    rw [BitVec.add_assoc, show ((12 : Word) + 4) = (16 : Word) from by decide]]
    at hmv28
  have hmv29 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 16) 4 _ rfl (by omega) (fun _ => rfl))
    (h := mv_spec_gen_within .x29 .x14 e (vf .x29) (base + 16) (by decide))
  rw [show (base + 16) + 4 = base + 20 from by
    rw [BitVec.add_assoc, show ((16 : Word) + 4) = (20 : Word) from by decide]]
    at hmv29
  have hadd30 := cpsTripleWithin_extend_code (cr' := CR)
    (hmono := by
      rw [hCR]
      exact mcg_mem base (base + 20) 5 _ rfl (by omega) (fun _ => rfl))
    (h := add_spec_gen_within .x30 .x28 .x29 m e (vf .x30) (base + 20)
      (by decide))
  rw [show (base + 20) + 4 = base + 24 from by
    rw [BitVec.add_assoc, show ((20 : Word) + 4) = (24 : Word) from by decide]]
    at hadd30
  -- frames + init chain
  have hmv5F := cpsTripleWithin_frameR
    (((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
      ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
      ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x6 : Reg) ↦ᵣ vf .x6) ** ((.x7 : Reg) ↦ᵣ vf .x7) **
      ((.x28 : Reg) ↦ᵣ vf .x28) ** ((.x29 : Reg) ↦ᵣ vf .x29) **
      ((.x30 : Reg) ↦ᵣ vf .x30) ** ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16))
    (by pcf) hmv5
  have hmv6F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x10 : Reg) ↦ᵣ v) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x7 : Reg) ↦ᵣ vf .x7) ** ((.x28 : Reg) ↦ᵣ vf .x28) **
      ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16))
    (by pcf) hmv6
  have hmv7F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x10 : Reg) ↦ᵣ v) **
      ((.x11 : Reg) ↦ᵣ r) ** ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ vf .x28) ** ((.x29 : Reg) ↦ᵣ vf .x29) **
      ((.x30 : Reg) ↦ᵣ vf .x30) ** ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16))
    (by pcf) hmv7
  have hmv28F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x14 : Reg) ↦ᵣ e) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x29 : Reg) ↦ᵣ vf .x29) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16))
    (by pcf) hmv28
  have hmv29F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x28 : Reg) ↦ᵣ m) ** ((.x30 : Reg) ↦ᵣ vf .x30) **
      ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16))
    (by pcf) hmv29
  have hadd30F := cpsTripleWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
      ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16))
    (by pcf) hadd30
  have hi1 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hmv5F hmv6F
  have hi2 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hi1 hmv7F
  have hi3 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hi2 hmv28F
  have hi4 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hi3 hmv29F
  have hi5 := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hi4 hadd30F
  -- ---- the input-overflow guard (station at base+24) ----
  have hbr6 := cpsBranchWithin_frameR
    (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
      ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
      ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) ** ((.x29 : Reg) ↦ᵣ e) **
      ((.x31 : Reg) ↦ᵣ vf .x31) **
      ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
      ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
    (by pcf)
    (cpsBranchWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 24) 6 _ rfl (by omega) (fun _ => rfl))
      (h := bltu_spec_gen_within .x30 .x28 (80 : BitVec 13) (m + e) m
        (base + 24)))
  rw [show (base + 24) + signExtend13 (80 : BitVec 13) = base + 104 from by
        rw [BitVec.add_assoc,
          show ((24 : Word) + signExtend13 (80 : BitVec 13)) = (104 : Word)
            from by decide],
      show (base + 24) + 4 = base + 28 from by
        rw [BitVec.add_assoc,
          show ((24 : Word) + (4 : Word)) = (28 : Word) from by decide]]
    at hbr6
  -- taken arm: the status-1 tail
  have htail1arm : BitVec.ult (m + e) m →
      cpsTripleWithin 21 (base + 104) ret CR
        (((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x28 : Reg) ↦ᵣ m) **
          (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x29 : Reg) ↦ᵣ e) **
            ((.x31 : Reg) ↦ᵣ vf .x31) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
        (mcgFullPost v r g m e ret) := by
    intro hOver
    have h := errTail_spec CR (base + 104) ret (1 : Word) v r g m
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ vf .x31) **
        ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
        ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) halignRet (by rw [hCR]; exact mcg_mem_err1 base)
    refine cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun h hp => by xperm_hyp hp)
        (fun h hq => ?_) h)
    unfold mcgFullPost mcgPost
    rw [if_pos hOver]
    unfold mcgOut
    have hq1 : (((.x5 : Reg) ↦ᵣ v) ** (((.x6 : Reg) ↦ᵣ r) **
        (((.x7 : Reg) ↦ᵣ g) ** (((.x28 : Reg) ↦ᵣ m) **
          (((.x29 : Reg) ↦ᵣ e) ** (((.x30 : Reg) ↦ᵣ (m + e)) **
            (((.x31 : Reg) ↦ᵣ vf .x31) ** (((.x15 : Reg) ↦ᵣ vf .x15) **
              (((.x16 : Reg) ↦ᵣ vf .x16) **
                (((.x10 : Reg) ↦ᵣ (1 : Word)) **
                 ((.x11 : Reg) ↦ᵣ (0 : Word)) **
                 ((.x12 : Reg) ↦ᵣ (0 : Word)) **
                 ((.x13 : Reg) ↦ᵣ (0 : Word)) **
                 ((.x14 : Reg) ↦ᵣ e) ** ((.x1 : Reg) ↦ᵣ ret) **
                 ((.x0 : Reg) ↦ᵣ (0 : Word)))))))))))) h := by
      xperm_hyp hq
    have hq2 := sepConj_mono (regIs_to_regOwn .x5 _)
      (sepConj_mono (regIs_to_regOwn .x6 _)
        (sepConj_mono (regIs_to_regOwn .x7 _)
          (sepConj_mono (regIs_to_regOwn .x28 _)
            (sepConj_mono (regIs_to_regOwn .x29 _)
              (sepConj_mono (regIs_to_regOwn .x30 _)
                (sepConj_mono (regIs_to_regOwn .x31 _)
                  (sepConj_mono (regIs_to_regOwn .x15 _)
                    (sepConj_mono (regIs_to_regOwn .x16 _)
                      (fun _ hh => hh))))))))) h hq1
    xperm_hyp hq2
  -- fall arm: stipend selection, the capping if, the .cap suffix
  have hfall6 : ¬ BitVec.ult (m + e) m →
      cpsTripleWithin 21 (base + 28) ret CR
        (((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x28 : Reg) ↦ᵣ m) **
          (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x29 : Reg) ↦ᵣ e) **
            ((.x31 : Reg) ↦ᵣ vf .x31) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
        (mcgFullPost v r g m e ret) := by
    intro hnOver
    -- li t6, 0
    have hli31 := cpsTripleWithin_extend_code (cr' := CR)
      (hmono := by
        rw [hCR]
        exact mcg_mem base (base + 28) 7 _ rfl (by omega) (fun _ => rfl))
      (h := li_spec_gen_within .x31 (vf .x31) (0 : Word) (base + 28)
        (by decide))
    rw [show (base + 28) + 4 = base + 32 from by
      rw [BitVec.add_assoc,
        show ((28 : Word) + 4) = (32 : Word) from by decide]] at hli31
    -- the stipend if (beq t0, x0 / lui+addiw)
    have hbr8 := cpsBranchWithin_frameR
      (((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
        ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ (0 : Word)) **
        ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
        ((.x1 : Reg) ↦ᵣ ret))
      (by pcf)
      (cpsBranchWithin_extend_code (cr' := CR)
        (hmono := by
          rw [hCR]
          exact mcg_mem base (base + 32) 8 _ rfl (by omega) (fun _ => rfl))
        (h := beq_spec_gen_within .x5 .x0 (12 : BitVec 13) v (0 : Word)
          (base + 32)))
    rw [show (base + 32) + signExtend13 (12 : BitVec 13) = base + 44 from by
          rw [BitVec.add_assoc,
            show ((32 : Word) + signExtend13 (12 : BitVec 13)) = (44 : Word)
              from by decide],
        show (base + 32) + 4 = base + 36 from by
          rw [BitVec.add_assoc,
            show ((32 : Word) + (4 : Word)) = (36 : Word) from by decide]]
      at hbr8
    -- taken (value zero): stipend = 0, nothing to do
    have hstipT : v = (0 : Word) →
        cpsTripleWithin 2 (base + 44) (base + 44) CR
          (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
            ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            ((.x31 : Reg) ↦ᵣ (0 : Word)) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret))
          (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
            ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            ((.x31 : Reg) ↦ᵣ stipend v) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret)) := by
      intro hv
      have hstay : cpsTripleWithin 2 (base + 44) (base + 44) CR
          (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
            ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            ((.x31 : Reg) ↦ᵣ (0 : Word)) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret))
          (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
            ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            ((.x31 : Reg) ↦ᵣ (0 : Word)) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret)) :=
        fun R _hR s _hcr h hpc => ⟨0, Nat.zero_le _, s, rfl, hpc, h⟩
      refine cpsTripleWithin_weaken (fun _ hp => hp) (fun h hq => ?_) hstay
      rw [show stipend v = (0 : Word) from by unfold stipend; rw [if_pos hv]]
      exact hq
    -- fall (value nonzero): lui + addiw materialize 2300
    have hstipF : ¬ v = (0 : Word) →
        cpsTripleWithin 2 (base + 36) (base + 44) CR
          (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
            ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            ((.x31 : Reg) ↦ᵣ (0 : Word)) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret))
          (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
            ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
            ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
            ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
            ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
            ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            ((.x31 : Reg) ↦ᵣ stipend v) **
            ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
            ((.x1 : Reg) ↦ᵣ ret)) := by
      intro hv
      have hlui := cpsTripleWithin_extend_code (cr' := CR)
        (hmono := by
          rw [hCR]
          exact mcg_mem base (base + 36) 9 _ rfl (by omega) (fun _ => rfl))
        (h := lui_spec_gen_within .x31 (0 : Word) (1 : BitVec 20) (base + 36)
          (by decide))
      rw [show ((((1 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend
            64 : Word) = (4096 : Word) from by decide,
          show (base + 36) + 4 = base + 40 from by
            rw [BitVec.add_assoc,
              show ((36 : Word) + 4) = (40 : Word) from by decide]] at hlui
      have haddiw := cpsTripleWithin_extend_code (cr' := CR)
        (hmono := by
          rw [hCR]
          exact mcg_mem base (base + 40) 10 _ rfl (by omega) (fun _ => rfl))
        (h := addiw_spec_gen_same_within .x31 (4096 : Word)
          (-1796 : BitVec 12) (base + 40) (by decide))
      rw [show ((((4096 : Word).truncate 32 : BitVec 32)
              + ((signExtend12 (-1796 : BitVec 12)).truncate 32 : BitVec 32)
              : BitVec 32).signExtend 64 : Word) = (2300 : Word) from by
            decide,
          show (base + 40) + 4 = base + 44 from by
            rw [BitVec.add_assoc,
              show ((40 : Word) + 4) = (44 : Word) from by decide]] at haddiw
      have hluiF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
          ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret))
        (by pcf) hlui
      have haddiwF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
          ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret))
        (by pcf) haddiw
      have hc := cpsTripleWithin_seq_perm_same_cr
        (fun _ hp => by xperm_hyp hp) hluiF haddiwF
      refine cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun h hq => ?_) hc
      rw [show stipend v = (2300 : Word) from by
        unfold stipend; rw [if_neg hv]]
      xperm_hyp hq
    -- merge the stipend if
    have hstip := cpsBranchWithin_merge_same_cr hbr8
      (cpsTripleWithin_weaken (fun h hq => by xperm_hyp hq)
        (fun _ hq => hq)
        (cpsTripleWithin_pure_pre (P := (v = (0 : Word)))
        (H := ((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
          ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
          ((.x31 : Reg) ↦ᵣ (0 : Word)) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret))
        hstipT))
      (cpsTripleWithin_weaken (fun h hq => by xperm_hyp hq)
        (fun _ hq => hq)
        (cpsTripleWithin_pure_pre (P := ¬ v = (0 : Word))
        (H := ((.x5 : Reg) ↦ᵣ v) ** ((.x0 : Reg) ↦ᵣ (0 : Word)) **
          ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
          ((.x29 : Reg) ↦ᵣ e) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
          ((.x31 : Reg) ↦ᵣ (0 : Word)) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret))
        hstipF))
    -- the capping if (station at base+44)
    have hbr11 := cpsBranchWithin_frameR
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
        ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x31 : Reg) ↦ᵣ stipend v) **
        ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf)
      (cpsBranchWithin_extend_code (cr' := CR)
        (hmono := by
          rw [hCR]
          exact mcg_mem base (base + 44) 11 _ rfl (by omega) (fun _ => rfl))
        (h := bltu_spec_gen_within .x7 .x30 (32 : BitVec 13) g (m + e)
          (base + 44)))
    rw [show (base + 44) + signExtend13 (32 : BitVec 13) = base + 76 from by
          rw [BitVec.add_assoc,
            show ((44 : Word) + signExtend13 (32 : BitVec 13)) = (76 : Word)
              from by decide],
        show (base + 44) + 4 = base + 48 from by
          rw [BitVec.add_assoc,
            show ((44 : Word) + (4 : Word)) = (48 : Word) from by decide]]
      at hbr11
    -- insufficient-gas arm: mv a3, t1 then the .cap join
    have hinsArm : BitVec.ult g (m + e) →
        cpsTripleWithin 16 (base + 76) ret CR
          (((.x7 : Reg) ↦ᵣ g) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
              ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
              ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
              ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
              ((.x29 : Reg) ↦ᵣ e) ** ((.x31 : Reg) ↦ᵣ stipend v) **
              ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
              ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
          (mcgFullPost v r g m e ret) := by
      intro hIns
      have hcap : capped r g (m + e) = r := by
        unfold capped
        rw [if_pos hIns]
      have hmv := cpsTripleWithin_extend_code (cr' := CR)
        (hmono := by
          rw [hCR]
          exact mcg_mem base (base + 76) 19 _ rfl (by omega) (fun _ => rfl))
        (h := mv_spec_gen_within .x13 .x6 r m (base + 76) (by decide))
      rw [show (base + 76) + 4 = base + 80 from by
        rw [BitVec.add_assoc,
          show ((76 : Word) + 4) = (80 : Word) from by decide]] at hmv
      have hmvF := cpsTripleWithin_frameR
        (((.x5 : Reg) ↦ᵣ v) ** ((.x7 : Reg) ↦ᵣ g) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x14 : Reg) ↦ᵣ e) **
          ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
          ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
        (by pcf) hmv
      have hfrom80 := from80_spec base ret v r g m e halignRet hnOver
      have hc := cpsTripleWithin_seq_perm_same_cr
        (fun h hp => by
          rw [hcap]
          have hp1 : (((.x15 : Reg) ↦ᵣ vf .x15) **
              ((((.x16 : Reg)) ↦ᵣ vf .x16) **
                (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
                 ((.x7 : Reg) ↦ᵣ g) ** ((.x10 : Reg) ↦ᵣ v) **
                 ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
                 ((.x13 : Reg) ↦ᵣ r) ** ((.x14 : Reg) ↦ᵣ e) **
                 ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
                 ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x31 : Reg) ↦ᵣ stipend v) **
                 ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))) h := by
            xperm_hyp hp
          have hp2 := sepConj_mono (regIs_to_regOwn .x15 _)
            (sepConj_mono (regIs_to_regOwn .x16 _)
              (fun _ hh => hh)) h hp1
          xperm_hyp hp2) hmvF hfrom80
      refine cpsTripleWithin_mono_nSteps (by omega)
        (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
          (fun _ hq => hq) hc)
    -- sufficient-gas arm: the capping else-path
    have helseArm : ¬ BitVec.ult g (m + e) →
        cpsTripleWithin 16 (base + 48) ret CR
          (((.x7 : Reg) ↦ᵣ g) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
            (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
              ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
              ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
              ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
              ((.x29 : Reg) ↦ᵣ e) ** ((.x31 : Reg) ↦ᵣ stipend v) **
              ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
              ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
          (mcgFullPost v r g m e ret) := by
      intro hnIns
      exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq)
        (elsePath_spec base ret v r g m e (vf .x15) (vf .x16) halignRet
          hnOver hnIns)
    -- the capping station
    have hstation11 := retJoinStation_spec
      (cond := BitVec.ult g (m + e))
      (PT := ((.x7 : Reg) ↦ᵣ g) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
        (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
          ((.x29 : Reg) ↦ᵣ e) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
      (PF := ((.x7 : Reg) ↦ᵣ g) ** ((.x30 : Reg) ↦ᵣ (m + e)) **
        (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) **
          ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
          ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
          ((.x14 : Reg) ↦ᵣ e) ** ((.x28 : Reg) ↦ᵣ m) **
          ((.x29 : Reg) ↦ᵣ e) ** ((.x31 : Reg) ↦ᵣ stipend v) **
          ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
          ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
      hbr11
      (fun h hq => by xperm_hyp hq)
      (fun h hq => by xperm_hyp hq)
      (fun hIns => hinsArm hIns)
      (fun hnIns => helseArm hnIns)
    -- li ; stipend-if ; capping station
    have hli31F := cpsTripleWithin_frameR
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) ** ((.x12 : Reg) ↦ᵣ g) **
        ((.x13 : Reg) ↦ᵣ m) ** ((.x14 : Reg) ↦ᵣ e) **
        ((.x28 : Reg) ↦ᵣ m) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x30 : Reg) ↦ᵣ (m + e)) **
        ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word)))
      (by pcf) hli31
    have hf1 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hli31F hstip
    have hf2 := cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hf1 hstation11
    exact cpsTripleWithin_mono_nSteps (by omega)
      (cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
        (fun _ hq => hq) hf2)
  -- the input-overflow station
  have hstation6 := retJoinStation_spec
    (cond := BitVec.ult (m + e) m)
    (PT := ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x28 : Reg) ↦ᵣ m) **
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
        ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x31 : Reg) ↦ᵣ vf .x31) **
        ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
    (PF := ((.x30 : Reg) ↦ᵣ (m + e)) ** ((.x28 : Reg) ↦ᵣ m) **
      (((.x5 : Reg) ↦ᵣ v) ** ((.x6 : Reg) ↦ᵣ r) ** ((.x7 : Reg) ↦ᵣ g) **
        ((.x10 : Reg) ↦ᵣ v) ** ((.x11 : Reg) ↦ᵣ r) **
        ((.x12 : Reg) ↦ᵣ g) ** ((.x13 : Reg) ↦ᵣ m) **
        ((.x14 : Reg) ↦ᵣ e) ** ((.x29 : Reg) ↦ᵣ e) **
        ((.x31 : Reg) ↦ᵣ vf .x31) **
        ((.x15 : Reg) ↦ᵣ vf .x15) ** ((.x16 : Reg) ↦ᵣ vf .x16) **
        ((.x1 : Reg) ↦ᵣ ret) ** ((.x0 : Reg) ↦ᵣ (0 : Word))))
    hbr6
    (fun h hq => by xperm_hyp hq)
    (fun h hq => by xperm_hyp hq)
    (fun hOver => htail1arm hOver)
    (fun hnOver => hfall6 hnOver)
  -- init ; station
  have hall := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hi5 hstation6
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => hq)
    (cpsTripleWithin_mono_nSteps (by omega) hall)

#print axioms multiRegRetTail_spec
#print axioms messageCallGas_spec

end MessageCallGasSAsm

end EvmAsm.Codegen
