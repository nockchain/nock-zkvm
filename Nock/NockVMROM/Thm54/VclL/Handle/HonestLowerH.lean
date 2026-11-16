/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestLowerH.lean

  Additive.

  `computeChipVCLH_sat_of_rows`: the compute chip `computeChipVCLH` accepts a trace as soon as its fixed
  columns bind the preprocessing and, at every row node, every gate of the `ℚ` base template vanishes (as
  `evalQ`) and every gate of the `ℚ` `𝕂` template vanishes (as `evalMQ`) at the gathered environment.  This
  is the converse of `base_of_sat` / `k_of_sat`: the `𝕂` gates are lowered through `mixedCompile_zero_iff`
  at `isCoordEnv_gather` (no randomness: `b` is a basis).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TeleC

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TeleC

open Nock Nock.Reified Nock.Framework
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.TeleH Nock.NockVMROM.Thm54.VclL.Handle.ServeH
open Module
open scoped Polynomial

noncomputable section

section Lower
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (P : Fin (computeChipVCLH hn nodes b chalV pubVal orbit).rap.w → F[X])

/-- **The compute chip accepts from its row gates.** -/
theorem computeChipVCLH_sat_of_rows
    (hbind : (computeChipVCLH hn nodes b chalV pubVal orbit).BindsPreprocessing P)
    (hbase : ∀ x ∈ rowNodeSet nodes, ∀ t ∈ baseGatesH (F := ℚ),
      evalQ t (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0)
    (hK : ∀ x ∈ rowNodeSet nodes, ∀ t ∈ kGatesH (F := ℚ),
      evalMQ t (Compute.TowerD.gatherEnv b (Reify.envOfTrace P orbit.ω x chalV pubVal))
        (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLH hn nodes b chalV pubVal orbit) P := by
  refine (computeChipVCLH_sat_iff hn nodes b chalV pubVal orbit P).mpr ⟨hbind, fun x hx g hg => ?_⟩
  unfold gatesH at hg
  rcases List.mem_append.mp hg with hb | hk
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
    rw [eval_mapC_cast]
    exact hbase x hx t ht
  · obtain ⟨m, hm, hmem⟩ := List.mem_flatMap.mp hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hmem
    have h1 : (mapM (fun q : ℚ => (q : F)) t).eval
        (Compute.TowerD.gatherEnv b (Reify.envOfTrace P orbit.ω x chalV pubVal))
        (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
      rw [eval_mapM_cast]; exact hK x hx t ht
    exact ((mixedCompile_zero_iff b Compute.TowerD.col0Id
      (Compute.TowerD.isCoordEnv_gather b (Reify.envOfTrace P orbit.ω x chalV pubVal)) _).mp h1) k

end Lower

end

end Nock.NockVMROM.Thm54.VclL.Handle.TeleC
