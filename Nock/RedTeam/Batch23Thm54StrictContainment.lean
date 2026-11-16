/-
  Nock/RedTeam/Batch23Thm54StrictContainment.lean

  `StrictContainment.production_falseAcceptance_le_at_char` is the same probability bound as
  `ProductionP8Containment.production_jointProbability_falseAcceptance_le` at `q = ringChar K`, but the
  caller no longer supplies `hcast : Set.InjOn (·:ℕ→K) (Iio q)`.  The discharging fact is Packet 2A's
  `StrictRawReconstruction.charCast_injOn`.  These regressions pin that the premise is really gone and
  that the discharging lemma is the one used.
-/

import Nock.NockVMROM.Thm54.StrictContainment

namespace Nock.RedTeam.Batch23

open Nock.NockVMROM.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **The characteristic-specialized containment bound, with `hcast` discharged.** Re-export of the
Packet 2 wrapper: the theorem's binder list carries no cast-injectivity argument. -/
alias b23_containment_hcast_free := StrictContainment.production_falseAcceptance_le_at_char

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- **The discharging lemma is cast-injectivity at the characteristic** (Packet 2A). This is exactly
the argument the wrapper feeds in place of the removed `hcast` binder. -/
theorem b23_discharger_is_charCast_injOn (p : ℕ) [CharP K p] :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio p) :=
  StrictRawReconstruction.charCast_injOn p

end Nock.RedTeam.Batch23
