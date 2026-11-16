/-
  Nock/RedTeam/Batch1582Thm54Route2DryRun.lean

  **Route-2 dry run (rule 4 (e)), replica fingerprints of a ChipData retarget.**
  A compute-slice `ChipDataC`, its
  package projection `toCD`, the generic `rowEnvAtD`, and for two DEFS — `FamilyEnvCore.rowEnvAt`
  (on the 701 frontier) and `StrategyOfTracesR0.computeEnvsR0` (not on it) — a verbatim replica and
  the route-2 wrapper; for one frontier THEOREM (`FamilyEnvCore.computeChipAt_width`) a replica with a changed
  proof.  Asserted (build fails otherwise):
  * the wrapper is definitionally the live definition (`rowEnvAt_w_eq`, `rfl`);
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! Route-2 dry run (ii): replica fingerprints. -/

open Lean Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open scoped Polynomial

namespace Nock.RedTeam.Batch1582

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- The compute-side chip data (route 2's `ChipData`, compute slice). -/
structure ChipDataC (F K : Type) [Field F] [Field K] [Algebra F K] (h : ℕ) where
  N : ℕ
  hN : 0 < N
  nodes : Fin N → F
  basis : Module.Basis (Fin 3) F K
  orbit : StrictExtension.StrictOrbitDomain F 3 h
  claim : P8PublicClaim
  pub : ℕ → F

def toCD (O : OptimizedStrictNockVMROMPackage F K hOrb) : ChipDataC F K hOrb where
  N := O.family.problem.cfg.compRows
  hN := O.family.problem.cfg.compRows_pos
  nodes := O.computeNodes
  basis := O.basis
  orbit := O.orbit
  claim := O.verifier.raw.claim
  pub := O.computePublic

/-- The generic env at chip data. -/
def rowEnvAtD (D : ChipDataC F K hOrb) (c : OptimizedProductionChallengeTuple K F) {w : ℕ}
    (Qc : Fin w → F[X]) (i : Fin D.N) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv D.basis
    (envOfTrace Qc D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c))

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- Verbatim replica of `FamilyEnvCore.rowEnvAt`. -/
def rowEnvAt_r (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X])
    (i : Fin O.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv O.basis
    (envOfTrace Qc O.orbit.ω (O.computeNodes i)
      (computeChalValOfTuple O.basis c)
      (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c))

/-- The route-2 wrapper of `FamilyEnvCore.rowEnvAt`. -/
def rowEnvAt_w (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X])
    (i : Fin O.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  rowEnvAtD (toCD O) c Qc i

/-- The wrapper is definitionally the original (so every downstream proof survives). -/
theorem rowEnvAt_w_eq (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes
      O.basis (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w
      → F[X]) (i : Fin O.family.problem.cfg.compRows) :
    rowEnvAt_w O c Qc i = FamilyEnvCore.rowEnvAt O c Qc i := rfl

/-- Verbatim replica of `StrategyOfTracesR0.computeEnvsR0`. -/
def computeEnvsR0_r (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos
      O.computeNodes O.basis O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Fin O.family.problem.cfg.compRows → Env K :=
  fun i => (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) i).toSourceEnv

/-- The wrapper form (through `rowEnvAtD`). -/
def computeEnvsR0_w (Qc : Fin (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos
      O.computeNodes O.basis O.computeChallenge O.computePublic O.orbit).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Fin O.family.problem.cfg.compRows → Env K :=
  fun i => (rowEnvAtD (toCD O) c (FamilyEnvCore.familyQc O c Qc) i).toSourceEnv

/-- Theorem replica of `FamilyEnvCore.computeChipAt_width` with a different proof. -/
theorem computeChipAt_width_r (c : OptimizedProductionChallengeTuple K F) :
    (DeployedChipFamily.computeChipAt O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      (computePublicOfTuple O.basis O.verifier.raw.claim O.computePublic c) O.orbit c).rap.w =
    (ProductionNamedComputeRAP O.family.problem.cfg.compRows_pos O.computeNodes O.basis
      O.computeChallenge O.computePublic O.orbit).rap.w :=
  (FamilyEnvCore.computeChipAt_width O c).trans rfl

end

end Nock.RedTeam.Batch1582


/-- Normalised hash: module-local `_proof_*` auxiliaries replaced by one placeholder. -/
def normHash (e : Lean.Expr) : UInt64 :=
  (e.replace fun x => match x with
    | .const n _ => match n with
      | .str _ s => if s.startsWith "_proof" then some (.const `AUXPROOF []) else none
      | _ => none
    | _ => none).hash

run_cmd do
  let env ← Lean.getEnv
  for (o, r, w) in [(`Nock.NockVMROM.Thm54.FamilyEnvCore.rowEnvAt, `Nock.RedTeam.Batch1582.rowEnvAt_r,
        `Nock.RedTeam.Batch1582.rowEnvAt_w),
      (`Nock.NockVMROM.Thm54.StrategyOfTracesR0.computeEnvsR0, `Nock.RedTeam.Batch1582.computeEnvsR0_r,
        `Nock.RedTeam.Batch1582.computeEnvsR0_w)] do
    let v := fun n => normHash ((env.find? n).get!.value!)
    let t := fun n => normHash ((env.find? n).get!.type)
    unless t o == t r && t o == t w do throwError "type hash mismatch at {o}"
    unless v o == v r do throwError "replica control failed at {o}"
    if v o == v w then throwError "wrapper did not change the value hash at {o}"
    Lean.logInfo m!"{o}: value live = replica {v o}; wrapper {v w} (moves)"
  let ty := fun n => ((env.find? n).get!.type).hash
  let a := ty `Nock.NockVMROM.Thm54.FamilyEnvCore.computeChipAt_width
  let b := ty `Nock.RedTeam.Batch1582.computeChipAt_width_r
  unless a == b do throwError "theorem meaning moved under a proof change"
  Lean.logInfo m!"computeChipAt_width: live = replica type hash {a} (theorem meaning is its type)"
