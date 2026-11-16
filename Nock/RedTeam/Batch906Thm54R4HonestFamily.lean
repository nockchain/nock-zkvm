/-
  Nock/RedTeam/Batch906Thm54R4HonestFamily.lean

  The honest instance of R4 is `c = P.honestTuple` with the canonical traces reindexed to the
  family width, `QcH = familyQc P c (canonicalComputeTrace P)`, `QmH = familyQm P c
  (canonicalMemoryTrace P)`.  The tuple cannot be moved off the honest fibre: the family chips
  read `requests` and the memory seed from fixed package publics, so away from the honest fibre
  the honest fill is rejected (`CoinParamCompleteness.exists_good_pole_rejected`, `Batch851`).

  What this file proves, at an arbitrary package `P` (generic in the program), from the named
  honest-fill hypotheses `HonestFill P` (the hypotheses of the existing canonical satisfaction
  theorems, `canonicalComputeTrace_satisfies` / `canonicalMemoryTrace_satisfies`, and of the
  chip-equality theorems `computeChipAt_honest_of_chalVal` / `memoryChipAt_honest_of_chalVal`):

  * `deployedAcceptance_honest` : `DeployedAcceptanceAt P P.honestTuple QcH QmH`;
  * `certBitsBoolean_honest` : `hb`, from acceptance (`Batch823.certBitsBoolean_of_sat`);
  * `h1_honest` : `coord b 1 0 ≠ 0`, from `FormRBasis`.

  Acceptance is stated as `RAP.SatisfiesWithPreprocessing (P.computeChipAt c)..` /
  `(P.memoryChipAt c)..` through `DeployedAcceptanceAt`.

  **`HonestFill` is not satisfied by the tree's fixture package.**  Its field `hchalM` (chip
  equality at the honest tuple, the premise of `memoryChipAt_honest_of_chalVal`) is false at the
  multi-root `F97` package: its raw memory scalar challenges are `j + 1` while the family chip
  reads `0` there (compiled: `Batch909.Fixture.packageP_hchalM_false`).  `Inputs.memoryScalarChallenge`
  is a free field of every generated package, so `hchalM` holds only where it is `0`.
-/
import Nock.RedTeam.Batch905Thm54R4HonestPremiseCensus
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch906

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

noncomputable section

/-! ## A. Transport of satisfaction along a chip equality -/

theorem sat_cast {F : Type} [Field F] {C₁ C₂ : FixedPreprocessingRAP F} (h : C₁ = C₂)
    (hw : C₁.rap.w = C₂.rap.w) (Q : Fin C₂.rap.w → F[X])
    (hQ : RAP.SatisfiesWithPreprocessing C₂ Q) :
    RAP.SatisfiesWithPreprocessing C₁ (fun j => Q (Fin.cast hw j)) := by
  subst h
  exact hQ

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## B. The honest traces at the family width -/

/-- The honest compute trace at the family chip's width. -/
def QcH : Fin (P.computeChipAt P.honestTuple).rap.w → F[X] :=
  familyQc P P.honestTuple (canonicalComputeTrace P)

/-- The honest memory trace at the family chip's width. -/
def QmH : Fin (P.memoryChipAt P.honestTuple).rap.w → F[X] :=
  familyQm P P.honestTuple (canonicalMemoryTrace P)

theorem honestQc_familyQc (c : OptimizedProductionChallengeTuple K F)
    (Q : Fin P.computeChip.rap.w → F[X]) : honestQc P c (familyQc P c Q) = Q := by
  funext j
  unfold honestQc familyQc
  apply congrArg Q
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem honestQm_familyQm (c : OptimizedProductionChallengeTuple K F)
    (Q : Fin P.memoryChip.rap.w → F[X]) : honestQm P c (familyQm P c Q) = Q := by
  funext j
  unfold honestQm familyQm
  apply congrArg Q
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem honestQc_QcH : honestQc P P.honestTuple (QcH P) = canonicalComputeTrace P :=
  honestQc_familyQc P _ _

theorem honestQm_QmH : honestQm P P.honestTuple (QmH P) = canonicalMemoryTrace P :=
  honestQm_familyQm P _ _

/-! ## C. The honest-fill hypotheses -/

/-- **The honest-fill hypotheses**: exactly the premises of the four existing theorems that carry
the canonical traces to satisfaction of the family chips at the honest tuple.  None is an event
statement.  At a generated package they are the generator's own obligations
(`FormRAxisBound` / `FormRBasis` / `FormRWidth` are `genComputeRows_rowsFormRAxisBound`,
`compilerBasis_formR`, `FormRWidth_of_hp64`; `hmore` is `later_seed_zeros`; `hC` the carrier's
`CprimeCoherent`; the chal / seed equalities are the package pins). -/
structure HonestFill : Prop where
  hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis
  hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis
  hwidth : OptimizedComputeFinalTrace.FormRWidth F
  hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
      (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
        (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0
  hC : P.optimized.family.problem.exec.CprimeCoherent
  hchalC : DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple =
    P.optimized.computeChallenge
  hchalM : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
    P.optimized.memoryChallenge
  hst : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state =
    ComputeWalkSeed.rootStateOfFormula P.optimized.verifier.raw.claim.formula
  hs : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
    GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.subject
  hf : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
    GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.formula
  he : (P.optimized.family.problem.exec.computePubAt
      ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
    GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.result

variable {P}

/-- **Acceptance at the family chips at the honest tuple.** -/
theorem deployedAcceptance_honest (H : HonestFill P) :
    DeployedAcceptanceAt P P.honestTuple (QcH P) (QmH P) := by
  have hC := P.computeChipAt_honest_of_chalVal H.hchalC H.hst H.hs H.hf H.he
  have hM := P.memoryChipAt_honest_of_chalVal H.hchalM
  have hQC := canonicalComputeTrace_satisfies P H.hax H.hbasis H.hwidth
  have hQM := canonicalMemoryTrace_satisfies P H.hmore H.hC
  have h1 := sat_cast hC (computeChipAt_width P P.honestTuple) (canonicalComputeTrace P) hQC
  have h2 := sat_cast hM (memoryChipAt_width P P.honestTuple) (canonicalMemoryTrace P) hQM
  exact ⟨h1, h2⟩

end

end Nock.RedTeam.Batch906

#print axioms Nock.RedTeam.Batch906.deployedAcceptance_honest
