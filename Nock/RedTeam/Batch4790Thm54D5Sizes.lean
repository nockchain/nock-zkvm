/-
  Nock/RedTeam/Batch4790Thm54D5Sizes.lean

  The pure and the jetted matmul `N = 2`
  evaluate to the same noun (kernel `decide +kernel`, no `native_decide`): on `AutogenMatmul.toyS` (the demo subject
  of `Demo.matProg`) both give `toyCG`, and on the sweep's subject `matS 2` both give `matRef 2` (the independent
  `ℕ` reference).
-/
import Nock.V1J8.D5Sizes

namespace Nock.RedTeam.Batch4790

open Nock Nock.V1J8.D5 Nock.Jet.Autogen

theorem pure_toyS : evalN 300 toyS (matPure 2) = some toyCG := by decide +kernel
theorem jet_toyS : evalN 301 toyS (matJetF 2) = some toyCG := by decide +kernel
theorem same_toyS : evalN 300 toyS (matPure 2) = evalN 301 toyS (matJetF 2) := by
  rw [pure_toyS, jet_toyS]

theorem pure_matS2 : evalN 300 (matS 2) (matPure 2) = some (matRef 2) := by decide +kernel
theorem jet_matS2 : evalN 301 (matS 2) (matJetF 2) = some (matRef 2) := by decide +kernel
theorem same_matS2 : evalN 300 (matS 2) (matPure 2) = evalN 301 (matS 2) (matJetF 2) := by
  rw [pure_matS2, jet_matS2]

#print axioms same_toyS
#print axioms same_matS2

end Nock.RedTeam.Batch4790
