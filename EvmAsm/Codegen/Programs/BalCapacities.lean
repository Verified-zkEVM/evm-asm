/-
  EvmAsm.Codegen.Programs.BalCapacities

  Named row-capacity contracts shared by the BAL producers and serializer.
  Keeping these values in one module prevents emitted callsites from quietly
  duplicating an arena bound as an unrelated assembly literal.
-/

namespace EvmAsm.Codegen

def balBuilderAccountCapacity : Nat := 140000
def balBuilderStorageChangeCapacity : Nat := 47522
/-- Block cold-storage bound: `200_000_000 / 3_000 = 66_666` (GH #11186 D4). -/
def balBuilderStorageReadsCapacity : Nat := 66666
def balBuilderBalanceCapacity : Nat := 105000
def balBuilderNonceCapacity : Nat := 35000
def balBuilderCodeCapacity : Nat := 13125

end EvmAsm.Codegen
