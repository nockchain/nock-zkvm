/-
  Nock/RedTeam/Batch495Thm54PrefixGammaEvents.lean

  Not yet in the consumed union.
-/
import Nock.NockVMROM.Thm54.WalkPrefixGammaEvents

set_option autoImplicit false

namespace Nock.RedTeam.Batch495

open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents

theorem compute_bound_eq (N : ℕ) : computePrefixGammaBound N = 9 * N :=
  computePrefixGammaBound_eq N

theorem memory_bound_eq (M : ℕ) : memoryPrefixGammaBound M = 5 * M :=
  memoryPrefixGammaBound_eq M

def cards : List (String × String) :=
  [("computePrefixGammaBound", "9N = N · (node_size − 1) at LT_comp width 10"),
    ("memoryPrefixGammaBound", "5M = M · (node_size − 1) at x^mem width 6"),
    ("committed", "computePrefixGammaEventOf_congr / memoryPrefixGammaEventOf_congr")]

theorem cards_length : cards.length = 3 := by decide

end Nock.RedTeam.Batch495

#print axioms Nock.RedTeam.Batch495.compute_bound_eq
#print axioms Nock.RedTeam.Batch495.memory_bound_eq
