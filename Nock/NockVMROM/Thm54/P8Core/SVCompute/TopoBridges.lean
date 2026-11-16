/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/TopoBridges.lean

  **The live `Batch453` / `Batch457` / `Batch459` / `Batch465` /
  `Batch471` / `Batch500` / `Batch1140` / `Batch1172` / `Batch823` / `WalkQueueDeployed` compute
  statements as corollaries of the route-2 twins at `toCD P.optimized`, `layout309`.**  Definition
  bridges (`rowOf`, `lnW`, `foW`, …) are `rfl`; theorem bridges apply the twin with the layout
  premises discharged (`rowFacts_of_sat`, `toCD_adjacent`, `pkgHchar P`).  Nothing live is edited.
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.IndexTwins
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChainBridges
import Nock.NockVMROM.Thm54.P8Core.Batch465Thm54DeployedRootLabelEqClaim
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.ComputeTable Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedComputeRows (pkgHchar)
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-! ## 1. -/

section Family

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)

theorem family_seed_slots_of_D (k : Fin 3) :
    P.familyComputePublic c (3 + (k : ℕ)) =
      CoordinateBasis.coord P.optimized.basis (seedOfClaim P.optimized.verifier.raw.claim c) k :=
  family_seed_slotsD (toCD P.optimized) c k

theorem rowOf_eq_D (i : ℕ) :
    Nock.RedTeam.Batch459.rowOf P i = rowOfD (toCD P.optimized) i := rfl

theorem rowOf_succ_of_D (k : ℕ) (hk : k < rows P) :
    Nock.RedTeam.Batch459.rowOf P (k + 1) = ⟨k, hk⟩ :=
  rowOf_succD (toCD P.optimized) k hk

theorem rowOf_one_of_D : Nock.RedTeam.Batch459.rowOf P 1 = firstRow P :=
  rowOf_oneD (toCD P.optimized)

theorem rowOf_rows_of_D : Nock.RedTeam.Batch459.rowOf P (rows P) = lastRow P :=
  rowOf_rowsD (toCD P.optimized)

theorem lnW_eq_D : Nock.RedTeam.Batch459.lnW P c Qc = lnWD (toCD P.optimized) layout309 c Qc := rfl

theorem countW_eq_D :
    Nock.RedTeam.Batch459.countW P c Qc = countWD (toCD P.optimized) layout309 c Qc := rfl

theorem accW_eq_D :
    Nock.RedTeam.Batch459.accW P c Qc = accWD (toCD P.optimized) layout309 c Qc := rfl

theorem curW_eq_D :
    Nock.RedTeam.Batch459.curW P c Qc hsat =
      curWD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P) := rfl

theorem chldW_eq_D :
    Nock.RedTeam.Batch459.chldW P c Qc hsat =
      chldWD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P) := rfl

theorem foW_eq_D :
    Nock.RedTeam.Batch459.foW P c Qc hsat =
      foWD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P) := rfl

/-- **`Batch459.deployed_walkSat` from the twin.** -/
theorem deployed_walkSat_of_D :
    WalkSat (Nock.RedTeam.Batch459.curW P c Qc hsat) (Nock.RedTeam.Batch459.chldW P c Qc hsat)
      (Nock.RedTeam.Batch459.foW P c Qc hsat) (Nock.RedTeam.Batch459.lnW P c Qc)
      (Nock.RedTeam.Batch459.countW P c Qc) (Nock.RedTeam.Batch459.accW P c Qc) (alphaC c.1)
      (seedOfClaim P.optimized.verifier.raw.claim c) (alphaC c.1) (rows P) :=
  deployed_walkSatD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P)
    (toCD_adjacent P.optimized)

include hsat in
theorem deployed_walk_out_of_D : Nock.RedTeam.Batch459.accW P c Qc (rows P) = 0 :=
  deployed_walk_outD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P)
    (toCD_adjacent P.optimized)

include hsat in
theorem notLast_at_of_D (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc i).baseTrace 12 = 0 :=
  notLast_walkD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P)
    (toCD_adjacent P.optimized) i hi

include hsat in
theorem walkLn_row0_of_D :
    (finalWalkLine .traceCur).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv = alphaC c.1 :=
  walkLn_row0D (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P)

theorem family_seed_at_of_D (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 1 = seedOfClaim P.optimized.verifier.raw.claim c :=
  family_seed_atD (toCD P.optimized) layout309 c Qc i

theorem family_initialCount_at_of_D (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 = alphaC c.1 :=
  family_initialCount_atD (toCD P.optimized) layout309 c Qc i

/-! ### `WalkQueueDeployed` (compute half) -/

include hsat in
theorem deployed_bfsValid_of_D :
    BFSValid (Nock.RedTeam.Batch459.foW P c Qc hsat) (rows P) :=
  deployed_bfsValidD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P)
    (toCD_adjacent P.optimized)

include hsat in
theorem count_eq_ln_last_of_D :
    Nock.RedTeam.Batch459.countW P c Qc (rows P) = Nock.RedTeam.Batch459.lnW P c Qc (rows P) :=
  count_eq_ln_lastD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) (pkgHchar P)
    (toCD_adjacent P.optimized)

end Family

/-! ## 2. -/

section Honest

variable (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (FamilyComputeRows.familyQc P c Qc₀))

theorem familyRow_trace_eq_of_D (i : Fin (rows P)) :
    (rowEnvAt P c (FamilyComputeRows.familyQc P c Qc₀) i).toSourceEnv.trace =
      (P.computeSourceEnv Qc₀ i).trace :=
  familyRow_trace_eqD (toCD P.optimized) layout309 c Qc₀ i

theorem familyRow_traceNext_eq_of_D (i : Fin (rows P)) :
    (rowEnvAt P c (FamilyComputeRows.familyQc P c Qc₀) i).toSourceEnv.traceNext =
      (P.computeSourceEnv Qc₀ i).traceNext :=
  familyRow_traceNext_eqD (toCD P.optimized) layout309 c Qc₀ i

theorem curOf_eq_curW_of_D (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    curOf (P.computeSourceEnv Qc₀) (gamma c.1) i =
      Nock.RedTeam.Batch459.curW P c (FamilyComputeRows.familyQc P c Qc₀) hsat i :=
  curOf_eq_curWD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat) (pkgHchar P) i
    hi1 hih

theorem chldOf_eq_chldW_of_D (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    chldOf (P.computeSourceEnv Qc₀) (gamma c.1) i l =
      Nock.RedTeam.Batch459.chldW P c (FamilyComputeRows.familyQc P c Qc₀) hsat i l :=
  chldOf_eq_chldWD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat) (pkgHchar P)
    i l hi1 hih

theorem foOf_eq_foW_of_D (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    foOf (P.computeSourceEnv Qc₀) i =
      Nock.RedTeam.Batch459.foW P c (FamilyComputeRows.familyQc P c Qc₀) hsat i :=
  foOf_eq_foWD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat) (pkgHchar P) i
    hi1 hih

theorem lblC_state'_of_D (i : ℕ) :
    (ExecOfTraces.lblC P Qc₀ c i).2.2.1.state = (ExecOfTraces.lblC P Qc₀ c i).1 :=
  lblC_state'D (toCD P.optimized) layout309 c Qc₀ i

theorem Vd_eq_D (i : ℕ) :
    Nock.RedTeam.Batch471.Vd P c Qc₀ i = VdD (toCD P.optimized) layout309 c Qc₀ i := rfl

theorem Cvd_eq_D (i l : ℕ) :
    Nock.RedTeam.Batch471.Cvd P c Qc₀ hsat i l =
      CvdD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat) (pkgHchar P) i l := rfl

include hsat in
theorem Vd_eq_committed_of_D (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    committedComputeV (P.computeSourceEnv Qc₀) i = Nock.RedTeam.Batch471.Vd P c Qc₀ i :=
  Vd_eq_committedD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat) (pkgHchar P) i
    hi1 hih

theorem Cvd_eq_committed_of_D (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ rows P) :
    committedComputeCv (P.computeSourceEnv Qc₀) i l =
      Nock.RedTeam.Batch471.Cvd P c Qc₀ hsat i l :=
  Cvd_eq_committedD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat) (pkgHchar P)
    i l hi1 hih

include hsat in
theorem deployed_walkSat_lblC_of_D :
    WalkSat (fun i => rlc (gamma c.1) (Nock.RedTeam.Batch471.Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Nock.RedTeam.Batch471.Cvd P c Qc₀ hsat i l))
      (ExecOfTraces.foC P Qc₀ c)
      (Nock.RedTeam.Batch459.lnW P c (FamilyComputeRows.familyQc P c Qc₀))
      (Nock.RedTeam.Batch459.countW P c (FamilyComputeRows.familyQc P c Qc₀))
      (Nock.RedTeam.Batch459.accW P c (FamilyComputeRows.familyQc P c Qc₀)) (alphaC c.1)
      (seedOfClaim P.optimized.verifier.raw.claim c) (alphaC c.1) (rows P) :=
  deployed_walkSat_lblCD (toCD P.optimized) layout309 c Qc₀ (rowFacts_of_sat P c _ hsat)
    (pkgHchar P) (toCD_adjacent P.optimized)

end Honest


/-! ## 3. -/

section Index

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])

theorem rowIdx_eq_D (i : ℕ) :
    Nock.RedTeam.Batch1140.rowIdx P i = rowIdxD (toCD P.optimized) i := rfl

theorem lblCS_succ_fst_of_D (m : ℕ) (hm : m < P.optimized.family.problem.cfg.compRows) :
    (StrategyOfTracesR0AC2.lblCS P.optimized (honestQc P c Qc) c (m + 1)).1.1 =
      StrategyOfTracesLift.computeStateOf
        (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc ⟨m, hm⟩)) :=
  lblCS_succ_fstD (toCD P.optimized) layout309 c (honestQc P c Qc) m hm

theorem computeArity_eq_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) :
    computeArity (Nock.RedTeam.Batch823.envsC P c Qc a) = rowArity (rowEnvAt P c Qc a) :=
  computeArity_eqD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) hchar a

theorem computePrefix_eq_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (a : Fin P.optimized.family.problem.cfg.compRows) :
    computePrefix (Nock.RedTeam.Batch823.envsC P c Qc) a = prefixExpAt P c Qc a :=
  computePrefix_eqD (toCD P.optimized) layout309 c Qc (rowFacts_of_sat P c Qc hsat) hchar a

end Index

end

end Nock.NockVMROM.Thm54.SVCompute
