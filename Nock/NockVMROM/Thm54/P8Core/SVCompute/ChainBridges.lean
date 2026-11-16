/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/ChainBridges.lean

  **The live `FamilyIOChain` chain theorems as corollaries of the
  route-2 twins (`ChainTwins`) at `toCD P.optimized`, `layout309`.**  Each `<name>_of_D` has the
  statement of the live package-typed theorem and is proved by the twin, with the layout premises
  (`hR`, `hs`, `hse`, `hL`, adjacency) discharged here — the discharge of `hL` is the receipt that
  `L.gates ⊆ chip gates` holds at `layout309` (`layout309_gatesOK`, `gates309_sub`).
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChainTwins
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainCompute
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.P8Core.SVCompute.PkgBridges
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F) (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-- The layout premises at `layout309`. -/
theorem layout309_nRoles_ok : 63 ≤ (layout309 (F := F) (K := K) (h := hOrb)).nRoles := le_refl _

theorem layout309_serial_eq :
    ((layout309 (F := F) (K := K) (h := hOrb)).serial : ℕ) = computeExpCol := rfl

theorem layout309_serialIsExp (D : ChipData F K hOrb) : SerialIsExp D layout309 :=
  fun _ hg => hg

/-- The row facts of an accepted live family trace. -/
theorem rowFacts_of_sat (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc) :
    RowFacts (toCD P.optimized) layout309 c Qc :=
  rowFacts_toCD P.optimized c Qc hsat

theorem chain_at_at_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc i).extTrace 60 = (rowEnvAt P c Qc i).extTraceNext 32 :=
  chain_at_atD (rowFacts_of_sat P c Qc hsat) i hi

theorem next_acc_at_of_D (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc i).extTraceNext 32 = (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩).extTrace 32 :=
  next_acc_atD (L := layout309) (toCD_adjacent P.optimized) layout309_nRoles_ok i hi

theorem acc_eq_prefixSum_at_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hden : ∀ (i : Fin (rows P)) (j : Fin 3), safeDenomWitness (rowEnvAt P c Qc i) j ≠ 0) :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnvAt P c Qc ⟨m, hm⟩).extTrace 32 = prefixSumAt P c Qc m :=
  acc_eq_prefixSum_atD (rowFacts_of_sat P c Qc hsat) (toCD_adjacent P.optimized)
    layout309_nRoles_ok hden

theorem ln_chain_at_at_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    lnCurAt (rowEnvAt P c Qc i) = lnPrevAt (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩) :=
  ln_chain_at_atD (rowFacts_of_sat P c Qc hsat) (toCD_adjacent P.optimized)
    layout309_nRoles_ok i hi

theorem totalRequestsAt_le_of_D : totalRequestsAt P c Qc ≤ 3 * rows P :=
  totalRequestsAt_leD (D := toCD P.optimized) (L := layout309) (c := c) (Q := Qc)

theorem lnPrev_at_at_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : nprSeed c.1 ≠ 0) :
    ∀ (m : ℕ) (hm : m < rows P),
      lnPrevAt (rowEnvAt P c Qc ⟨m, hm⟩) = ln0At P c Qc * chipAlphaAt c ^ prefixExpAt P c Qc m :=
  lnPrev_at_atD (rowFacts_of_sat P c Qc hsat) (toCD_adjacent P.optimized)
    layout309_nRoles_ok hchar hz0

theorem expCol_step_at_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩).expCol =
      (rowEnvAt P c Qc i).expCol + ((rowArity (rowEnvAt P c Qc i) : ℕ) : F) :=
  expCol_step_atD (rowFacts_of_sat P c Qc hsat) (layout309_gatesOK _) (toCD_adjacent P.optimized)
    layout309_serial_eq (layout309_serialIsExp _) hchar i hi

theorem expCol_eq_prefixExp_at_of_D (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ (m : ℕ) (hm : m < rows P),
      (rowEnvAt P c Qc ⟨m, hm⟩).expCol = ((prefixExpAt P c Qc m : ℕ) : F) :=
  expCol_eq_prefixExp_atD (rowFacts_of_sat P c Qc hsat) (layout309_gatesOK _)
    (toCD_adjacent P.optimized) layout309_serial_eq (layout309_serialIsExp _) hchar

end

end Nock.NockVMROM.Thm54.SVCompute
