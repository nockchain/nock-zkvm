/-
  Nock/RedTeam/Batch315Thm54ChipIdentityNonvacuous.lean

  After the sampled-pole retarget that hypothesis is
  inhabited as soon as the sampled pole is nonzero, even on a zero record.

  Paper at source: the paper.
-/
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryInternalPole

namespace Nock.RedTeam.Batch315

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54.MemoryPaperFactorization
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis hiding poleSource
open Nock.NockVMROM.Thm54.MemoryInternalPole

/-- Zero record, `γ = 0` (slot 4), sampled pole at slot 6. -/
def zeroRecordSampledPole (pole : ℚ) : Env ℚ where
  trace := fun _ => 0
  traceNext := fun _ => 0
  chal := fun i => if i = 6 then pole else 0
  pub := fun _ => 0

/-- Slot 6 is the sampled pole on this environment -/
theorem chal6_is_sampled_pole (pole : ℚ) :
    (zeroRecordSampledPole pole).chal 6 = pole := by
  simp [zeroRecordSampledPole]

/-- Paper-shaped `poleSource` is `chal 6 + recordRLC` -/
theorem paper_poleSource_is_chal6_plus_rlc :
    poleSource =
      Expr.Add (.Var .challenge 6) recordRLCExpr :=
  rfl

/-- On a zero record, `recordRLC` vanishes (every trace role is 0) -/
theorem recordRLC_zero_at_zero_record (pole : ℚ) :
    recordRLCExpr.eval (zeroRecordSampledPole pole) = 0 := by
  simp [recordRLCExpr, Expr.eval, zeroRecordSampledPole]

/-- At a zero record the compress is the sampled pole -/
theorem poleSource_at_zero_record_eq_interPole (pole : ℚ) :
    poleSource.eval (zeroRecordSampledPole pole) = pole := by
  simp [poleSource, recordRLCExpr, Expr.eval, zeroRecordSampledPole]

/-- `hpole` holds on a zero-record row once the sampled pole is nonzero. -/
theorem hpole_holds_at_zero_record_of_interPole_ne (pole : ℚ) (h : pole ≠ 0) :
    poleSource.eval (zeroRecordSampledPole pole) ≠ 0 := by
  simpa [poleSource_at_zero_record_eq_interPole] using h

theorem vacuity_is_the_zero_pole_case :
    poleSource.eval (zeroRecordSampledPole 0) = 0 :=
  poleSource_at_zero_record_eq_interPole 0

theorem chipInterCoins_are_sampled {K : Type} [Field K] (envK : Env K) :
    chipInterCoins envK = ⟨envK.chal 4, envK.chal 6⟩ :=
  rfl

end Nock.RedTeam.Batch315

#print axioms Nock.RedTeam.Batch315.poleSource_at_zero_record_eq_interPole
#print axioms Nock.RedTeam.Batch315.hpole_holds_at_zero_record_of_interPole_ne
#print axioms Nock.RedTeam.Batch315.vacuity_is_the_zero_pole_case
#print axioms Nock.RedTeam.Batch315.chipInterCoins_are_sampled
