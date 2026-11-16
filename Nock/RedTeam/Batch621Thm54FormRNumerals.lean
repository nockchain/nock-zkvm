/-
  Nock/RedTeam/Batch621Thm54FormRNumerals.lean

  Compute `302 / 416`, memory `204 / 156`, challenge space `|𝕂|¹¹`, `λ` at memory slot `8`
  / compute slot `9`, read off the deployed objects.  Axioms of `of_package` and
  `nockCompiles_zmod` are printed below (whitelist).
-/
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch621

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Module

theorem numerals {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [Fintype F]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (OptimizedComputeCorrectedFinal.ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w
        = 303 ∧
      (OptimizedComputeCorrectedFinal.ProductionNamedComputeRAP hn nodes b chalVal pubVal
        orbit).rap.s = 418 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.w = 205 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.s = 156 ∧
      Fintype.card (OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) =
        Fintype.card K ^ 11 :=
  ⟨rfl, computeChip_s hn nodes b chalVal pubVal orbit,
    (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit kMem).1,
    memoryChip_s hn nodes b chalVal pubVal orbit kMem,
    FormRAxisEvent.landed_card K F⟩

end Nock.RedTeam.Batch621

#print axioms Nock.RedTeam.Batch621.numerals
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
