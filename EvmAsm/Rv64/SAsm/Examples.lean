/-
  EvmAsm.Rv64.SAsm.Examples

  Flattening sanity checks for the SAsm DSL (Milestone 1): concrete programs
  through `size` / `flatten` / `offsetsOk`, checked by `#guard` so drift in
  the layout rules fails the build.
-/

import EvmAsm.Rv64.SAsm.Flatten

namespace EvmAsm.Rv64
namespace SAsm
namespace Examples

open Stmt

/-- init; bounded count-up loop; conditional move. -/
private def demoLoop : Stmt :=
  .block "init" [.LI .x5 0, .LI .x6 10] ;;;
  .«while» "count" (.bltu .x5 .x6) 10
      (fun i rf _ => rf.get .x5 = BitVec.ofNat 64 i)
      (.block "step" [.ADDI .x5 .x5 1]) ;;;
  .assert "counted" (fun rf _ => rf.get .x5 = 10) ;;;
  .when "nonzero" (.bne .x5 .x0) (.block "mv" [.MV .x10 .x5])

#guard demoLoop.size = 7
#guard demoLoop.offsetsOk

/- Expected layout at any base (position-independent: no calls):
      0: LI   x5, 0
      4: LI   x6, 10
      8: BGEU x5, x6, +12      -- while header (negated bltu), exit past body
     12: ADDI x5, x5, 1
     16: JAL  x0, -8           -- back to header
     20: BEQ  x5, x0, +8       -- when (negated bne), skip body
     24: MV   x10, x5                                                     -/
#guard demoLoop.flatten 0x1000 =
  [.LI .x5 0, .LI .x6 10,
   .BGEU .x5 .x6 (12 : BitVec 13),
   .ADDI .x5 .x5 1,
   .JAL .x0 (BitVec.ofInt 21 (-8)),
   .BEQ .x5 .x0 (8 : BitVec 13),
   .MV .x10 .x5]

/-- ite: check-and-select. -/
private def demoIte : Stmt :=
  .ite "select" (.bltu .x10 .x11)
    (.block "lo" [.MV .x12 .x10])
    (.block "hi" [.MV .x12 .x11])

#guard demoIte.size = 4
#guard demoIte.offsetsOk

/- Expected layout:
      0: BGEU x10, x11, +12    -- to else
      4: MV   x12, x10
      8: JAL  x0, +8           -- over else
     12: MV   x12, x11                                                    -/
#guard demoIte.flatten 0x1000 =
  [.BGEU .x10 .x11 (12 : BitVec 13),
   .MV .x12 .x10,
   .JAL .x0 (8 : BitVec 21),
   .MV .x12 .x11]

/- A call resolves to a pc-relative JAL (stub handle: layout-only demo). -/
private def demoCall : Stmt :=
  .block "arg" [.LI .x10 42] ;;; .call "helper" (.stub 0x2000)

#guard demoCall.size = 2
#guard demoCall.flatten 0x1800 =
  [.LI .x10 42, .JAL .x1 (0x7FC : BitVec 21)]  -- 0x2000 - 0x1804

/- `assert` emits no code and does not perturb downstream addresses. -/
#guard (Stmt.assert "mid" (fun rf _ => rf.get .x5 = 0)).size = 0
#guard (Stmt.assert "mid" (fun rf _ => rf.get .x5 = 0)).flatten 0x1000 = []

end Examples
end SAsm
end EvmAsm.Rv64
