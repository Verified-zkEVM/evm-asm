/-
  EvmAsm.Rv64.SAsm.GlobalDataDemo

  End-to-end demo of the global-data footprint model (bead evm-asm-85699),
  mirroring the AbiFrame demos: a synthetic leaf routine that

  ```
    la  t0, CONST      -- auipc x5, %pcrel_hi ; addi x5, x5, %pcrel_lo
    ld  t1, 0(t0)      -- read the read-only constant
    la  t2, CELL       -- auipc x7, %pcrel_hi ; addi x7, x7, %pcrel_lo
    sd  t1, 0(t2)      -- write it into the RW scratch cell
    ret
  ```

  with code at `0x80001000`, the constant global at `0x80040000`, and the
  RW cell at `0x80040008`.  The `%pcrel_hi`/`%pcrel_lo` immediates are
  COMPUTED by `laHi`/`laLo` and `#guard`-tied to the hand-written literal
  program (hi 63, lo 0 and hi 63, lo −4) — the emitter formula reproduces the exact
  bytes.  `gdDemo_spec` proves the genuine post: `t1` observed the
  constant, the constant global is unchanged, and the RW cell now holds
  it.  Addresses are materialized by `la_materialize_within` — proven, not
  assumed.
-/

import EvmAsm.Rv64.SAsm.GlobalData
import EvmAsm.Rv64.SAsm.FramePort
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

namespace GlobalDataDemo

/-- Code base, constant global, RW scratch cell (synthetic layout). -/
def demoBase : Word := 0x80001000
def demoConstAddr : Word := 0x80040000
def demoCellAddr : Word := 0x80040008

/-- The demo routine, immediates computed by the `la` resolution model. -/
def gdDemo_prog : Program :=
  [ .AUIPC .x5 (laHi demoBase demoConstAddr),
    .ADDI .x5 .x5 (laLo demoBase demoConstAddr),
    .LD .x6 .x5 (0 : BitVec 12),
    .AUIPC .x7 (laHi (demoBase + 12) demoCellAddr),
    .ADDI .x7 .x7 (laLo (demoBase + 12) demoCellAddr),
    .SD .x7 .x6 (0 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Byte identity (kernel-checked): the computed `%pcrel_hi`/`%pcrel_lo`
    immediates ARE the hand-written literals an assembler would emit. -/
theorem gdDemo_prog_eq : gdDemo_prog =
    [ .AUIPC .x5 (63 : BitVec 20), .ADDI .x5 .x5 (0 : BitVec 12),
      .LD .x6 .x5 (0 : BitVec 12),
      .AUIPC .x7 (63 : BitVec 20), .ADDI .x7 .x7 (-4 : BitVec 12),
      .SD .x7 .x6 (0 : BitVec 12),
      .JALR .x0 .x1 (0 : BitVec 12) ] := rfl

-- Both `la` displacements are representable.
#guard decide (laInRange demoBase demoConstAddr)
#guard decide (laInRange (demoBase + 12) demoCellAddr)

/-- **The demo spec** (genuine post): after the routine, `t1` holds the
    constant `K`, the read-only global still holds `K`, and the RW scratch
    cell has been UPDATED from `old` to `K`.  Both global addresses were
    materialized by the proven `la` model. -/
theorem gdDemo_spec (K old ret v5 v6 v7 : Word)
    (halign : (ret &&& ~~~(1 : Word)) = ret) :
    cpsTripleWithin 7 demoBase ret (CodeReq.ofProg demoBase gdDemo_prog)
      ((.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** ((.x1 : Reg) ↦ᵣ ret) **
        globalCellIs demoConstAddr K ** globalCellIs demoCellAddr old)
      ((.x5 ↦ᵣ demoConstAddr) ** (.x6 ↦ᵣ K) ** (.x7 ↦ᵣ demoCellAddr) **
        ((.x1 : Reg) ↦ᵣ ret) **
        globalCellIs demoConstAddr K ** globalCellIs demoCellAddr K) := by
  unfold globalCellIs
  -- la t0, CONST (2 steps, address proven by la_resolve)
  have hla1 := la_materialize_within .x5 v5 demoBase demoConstAddr
    (cr := CodeReq.ofProg demoBase gdDemo_prog)
    (by decide) (by decide) (by code_mem) (by code_mem)
  -- ld t1, 0(t0)
  have hld := liftCode (cr' := CodeReq.ofProg demoBase gdDemo_prog)
    (ld_spec_within .x6 .x5 demoConstAddr v6 K (0 : BitVec 12) (demoBase + 8)
      (by decide))
    (by code_mem)
  rw [show demoConstAddr + signExtend12 (0 : BitVec 12) = demoConstAddr from by decide,
    show (demoBase + 8 : Word) + 4 = demoBase + 12 from by decide] at hld
  -- la t2, CELL
  have hla2 := la_materialize_within .x7 v7 (demoBase + 12) demoCellAddr
    (cr := CodeReq.ofProg demoBase gdDemo_prog)
    (by decide) (by decide) (by code_mem) (by code_mem)
  rw [show (demoBase + 12 : Word) + 8 = demoBase + 20 from by decide] at hla2
  -- sd t1, 0(t2)
  have hsd := liftCode (cr' := CodeReq.ofProg demoBase gdDemo_prog)
    (sd_spec_within .x7 .x6 demoCellAddr K old (0 : BitVec 12) (demoBase + 20))
    (by code_mem)
  rw [show demoCellAddr + signExtend12 (0 : BitVec 12) = demoCellAddr from by decide,
    show (demoBase + 20 : Word) + 4 = demoBase + 24 from by decide] at hsd
  -- ret
  have hret := liftCode (cr' := CodeReq.ofProg demoBase gdDemo_prog)
    (EvmAsm.Evm64.ret_spec_within' (demoBase + 24) ret)
    (by code_mem)
  rw [halign] at hret
  -- frames + chain
  have hla1F := cpsTripleWithin_frameR
    ((.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** ((.x1 : Reg) ↦ᵣ ret) **
      (demoConstAddr ↦ₘ K) ** (demoCellAddr ↦ₘ old)) (by pcf) hla1
  have hldF := cpsTripleWithin_frameR
    ((.x7 ↦ᵣ v7) ** ((.x1 : Reg) ↦ᵣ ret) ** (demoCellAddr ↦ₘ old)) (by pcf) hld
  have hla2F := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ demoConstAddr) ** (.x6 ↦ᵣ K) ** ((.x1 : Reg) ↦ᵣ ret) **
      (demoConstAddr ↦ₘ K) ** (demoCellAddr ↦ₘ old)) (by pcf) hla2
  have hsdF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ demoConstAddr) ** ((.x1 : Reg) ↦ᵣ ret) ** (demoConstAddr ↦ₘ K))
    (by pcf) hsd
  have hretF := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ demoConstAddr) ** (.x6 ↦ᵣ K) ** (.x7 ↦ᵣ demoCellAddr) **
      (demoConstAddr ↦ₘ K) ** (demoCellAddr ↦ₘ K)) (by pcf) hret
  have c1 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) hla1F hldF
  have c2 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c1 hla2F
  have c3 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c2 hsdF
  have c4 := cpsTripleWithin_seq_perm_same_cr (fun _ hp => by xperm_hyp hp) c3 hretF
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) c4

#print axioms gdDemo_spec

end GlobalDataDemo

end EvmAsm.Rv64.SAsm
