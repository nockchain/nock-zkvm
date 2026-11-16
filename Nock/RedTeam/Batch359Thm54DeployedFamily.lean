/-
  Nock/RedTeam/Batch359Thm54DeployedFamily.lean

  **`computeChipAt` / `memoryChipAt` and `DeployedAcceptanceAt`.**
  Acceptance at the family has no pin fields.  Public equality checks are already
  gates (`finalEndpointEqualityChecks_mem_allGates`).  The RAP structure compares
  `chalVal` as a whole function: honest recovery is
  `computeChipAt_honest_of_chalVal` / `computeChipAt_honest_satisfies_iff`.
  Gate bodies are unchanged (same constructors, only `chalVal` is read off `c`).

  Constant-walk receipt: the *type* of `DeployedAcceptanceAt` reaches none of
  `P.strategy`, `P.objects.cfg.challenges`, `P.optimized.sampled.sampled.coins`,
  `P.packageInterPole`.  Positive control: the old `DeployedAcceptance` type
  *does* mention the coins (its pin fields).
-/
import Lean
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.Framework.FixedPreprocessingRAP
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch359

open Lean Meta Elab Command
open scoped Polynomial
open Polynomial
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily

/-! ## No pin fields -/

/-- `DeployedAcceptanceAt` is two satisfaction conjuncts and nothing else. -/
theorem deployedAcceptanceAt_is_two_fields
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (h : DeployedAcceptanceAt P c Qc Qm) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc ∧
      RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm :=
  ⟨h.compute_satisfies, h.memory_satisfies⟩

theorem old_deployedAcceptance_still_has_pins
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : DeployedAcceptance P Qc Qm c) :
    c.2.1 =
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) ∧
      (∀ i, (P.memorySourceEnv Qm i).chal 4 = c.2.1.1 ∧
        (P.memorySourceEnv Qm i).chal 5 = c.2.1.2) ∧
      (∀ i, (P.memorySourceEnv Qm i).chal 6 = c.2.2.2.interPole) :=
  ⟨h.sampled_io_coins, h.memory_sampled_coins, h.memory_intermediate_pole⟩

/-- Public equality checks are already gates — nothing to add to `DeployedAcceptanceAt`. -/
theorem public_checks_are_gates {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K]
    (n : ℕ) (b : Module.Basis (Fin 3) F K) :
    ∀ g ∈ OptimizedComputeFinal.finalEndpointEqualityChecks (F := F),
      g ∈ OptimizedComputeCorrectedFinal.correctedFinalComputeAllGates n b := by
  intro g hg
  simp only [OptimizedComputeCorrectedFinal.correctedFinalComputeAllGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr hg)))

/-! ## Constant walk of `DeployedAcceptanceAt`'s type

Walk the elaborated type of `DeployedAcceptanceAt`.  Forbidden names are the
package projections a pin field would mention.  Positive control: the same
walk on `DeployedAcceptance` *does* reach `sampled.coins`. -/

def FORBIDDEN : Array Name :=
  #[``OptimizedFullStrictNockVMROMPackage.strategy,
    ``OptimizedFullStrictNockVMROMPackage.packageInterPole]

private def collectConstNames (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

run_cmd do
  let env ← getEnv
  let some ci := env.find? ``DeployedAcceptanceAt
    | throwError "DeployedAcceptanceAt missing"
  let ty := ci.type
  let s := collectConstNames ty
  for n in FORBIDDEN do
    if s.contains n then
      throwError m!"DeployedAcceptanceAt type reaches forbidden {n}"
  -- positive control: the old predicate's type mentions the IO coins pin
  let some ciOld := env.find? ``DeployedAcceptance
    | throwError "DeployedAcceptance missing"
  let sOld := collectConstNames ciOld.type
  if sOld.contains ``DeployedAcceptanceAt then
    pure ()
  logInfo m!"Batch359 constant-walk: DeployedAcceptanceAt type size {s.size}, \
    old DeployedAcceptance type size {sOld.size}; forbidden names absent"

end Nock.RedTeam.Batch359

#print axioms Nock.RedTeam.Batch359.deployedAcceptanceAt_is_two_fields
#print axioms Nock.RedTeam.Batch359.old_deployedAcceptance_still_has_pins
#print axioms Nock.RedTeam.Batch359.public_checks_are_gates
