/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestSatX.lean

  **`sat_iff` for
  `computeChipVCLHX`** (twin of `ComputeSatHQ.computeChipVCLHQ_sat_iff`).  Additive: a NEW module.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComputeSatHQ
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HonestSatX

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **`sat_iff` for `computeChipVCLHX`**: satisfaction with preprocessing is the preprocessing binding
plus every gate of `gatesHX` at every row node. -/
theorem computeChipVCLHX_sat_iff {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX hn nodes b δ chalV pubVal orbit) P ↔
      (computeChipVCLHX hn nodes b δ chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ gatesHX b δ,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.compose P i).eval x =
        ((gatesHX b δ).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

end

end Nock.NockVMROM.Thm54.VclL.Handle.HonestSatX
