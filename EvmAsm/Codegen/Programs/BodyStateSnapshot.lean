/-
  EvmAsm.Codegen.Programs.BodyStateSnapshot

  Source-level emitters for the canonical body-state snapshot slab.  These
  produce the existing straight-line instructions; they are deliberately not
  guest subroutines, so root and child capture retain their exact instruction
  order and rollback timing.
-/

namespace EvmAsm.Codegen

/-- Emit one scalar capture into a field of a body-state snapshot record.
    The caller chooses scratch registers so the generated instruction sequence
    remains identical at each existing capture site. -/
def bodyStateCaptureScalarAsm (sourceLabel destinationReg : String) (destinationOffset : Nat)
    (addressReg valueReg : String) : String :=
  "  la " ++ addressReg ++ ", " ++ sourceLabel ++ "; ld " ++ valueReg ++ ", 0(" ++
    addressReg ++ "); sd " ++ valueReg ++ ", " ++ toString destinationOffset ++
    "(" ++ destinationReg ++ ")\n"

/-- Emit the three live environment cursors into their canonical snapshot
    fields.  `sourceSetup` is either the root environment address materialiser
    or the empty prefix for a frame-local environment register. -/
def bodyStateCaptureCursorsAsm (sourceSetup sourceEnvReg destinationReg valueReg : String) : String :=
  sourceSetup ++ "ld " ++ valueReg ++ ", 448(" ++ sourceEnvReg ++ "); sd " ++ valueReg ++
    ", 40(" ++ destinationReg ++ "); ld " ++ valueReg ++ ", 464(" ++ sourceEnvReg ++
    "); sd " ++ valueReg ++ ", 48(" ++ destinationReg ++ "); ld " ++ valueReg ++
    ", 472(" ++ sourceEnvReg ++ "); sd " ++ valueReg ++ ", 56(" ++ destinationReg ++ ")\n"

end EvmAsm.Codegen
