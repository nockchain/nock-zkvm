import Nock.NockVMROM.Thm54.VclL.Compute.TowerComplete

/-!
# Route (d), TWD-4 item (d) : `sat_iff` of the tower chip and the gate-list transport

`vclGatesQ7T_iff`: the tower gate list is accepted at
a VCL row `envV` iff the kept typed gates hold in `𝕂′` at the pull-back, the serial / `ax` / `ax`-Im
gates hold, the three slot pairs vanish over `𝕂′` and the accumulator gates hold.
`computeChipVCLQ7T_sat_iff` is the copy of `computeChipVCLQ7S_sat_iff`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
  Nock.Framework.Reify

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section GateIff
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The tower row semantics at a VCL row `envV`.** -/
structure TowerRowHolds (b : Basis (Fin 3) F K) (n : ℕ) (envV : Env F) : Prop where
  kept : TowerKeptHolds n δ (gatherEnv b (pullEnv envV)) (pullEnv envV)
  serial : ∀ g ∈ (serialGates : List (CoeffExpr F)), g.eval envV = 0
  ax : ∀ g ∈ axGates b ++ axImGates, g.eval envV = 0
  slot0 : Q.IsZero (slot0Q F δ) (gatherEnv b envV) envV
  slot1 : Q.IsZero (slot1Q F δ) (gatherEnv b envV) envV
  slot2 : Q.IsZero (slot2Q F δ) (gatherEnv b envV) envV
  acc : ∀ g ∈ (accGatesT : List (CoeffExpr F)), g.eval envV = 0
  /-- The `z1` gates. -/
  z1 : ∀ g ∈ z1Gates b δ, g.eval envV = 0

theorem lookupGatesT_iff (b : Basis (Fin 3) F K) (envV : Env F) :
    (∀ g ∈ lookupGatesT b δ, g.eval envV = 0) ↔
      Q.IsZero (slot0Q F δ) (gatherEnv b envV) envV ∧ Q.IsZero (slot1Q F δ) (gatherEnv b envV) envV ∧
        Q.IsZero (slot2Q F δ) (gatherEnv b envV) envV := by
  have hc := isCoordEnv_gather b envV
  rw [← qGates_iff b hc, ← qGates_iff b hc, ← qGates_iff b hc]
  simp only [lookupGatesT, List.mem_append]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Or.inl (Or.inl hg)), fun g hg => h g (Or.inl (Or.inr hg)),
      fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨h0, h1, h2⟩ g ((hg | hg) | hg)
    exacts [h0 g hg, h1 g hg, h2 g hg]

/-- The kept part of the tower list, reindexed, is accepted at `envV` iff the unreindexed list is
accepted at the pull-back. -/
theorem keptT_reindex_iff (n e : ℕ) (b : Basis (Fin 3) F K) (envV : Env F) :
    (∀ g ∈ (towerKeptGates n e b δ).map reindexE, g.eval envV = 0) ↔
      ∀ g ∈ towerKeptGates n e b δ, g.eval (pullEnv envV) = 0 := by
  have key : ∀ g ∈ towerKeptGates n e b δ, (reindexE g).eval envV = g.eval (pullEnv envV) :=
    fun g hg => eval_reindexE g (pullEnv envV) envV (towerKeptGates_colsIn n e b δ g hg)
      (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
  constructor
  · intro h g hg
    rw [← key g hg]; exact h _ (List.mem_map_of_mem hg)
  · intro h g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    rw [key g' hg']; exact h g' hg'

/-- **The tower gate list, transported.** -/
theorem vclGatesQ7T_iff (b : Basis (Fin 3) F K) (n e : ℕ) (he : e = MemoryTable.pwScaleExp K)
    (envV : Env F) :
    (∀ g ∈ vclGatesQ7T n e b δ, g.eval envV = 0) ↔ TowerRowHolds δ b n envV := by
  rw [vclGatesQ7T]
  simp only [List.mem_append]
  constructor
  · intro h
    have hk : ∀ g ∈ (towerKeptGates n e b δ).map reindexE, g.eval envV = 0 := fun g hg =>
      h g (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hg)))))
    have hl : ∀ g ∈ lookupGatesT b δ, g.eval envV = 0 := fun g hg => h g (Or.inl (Or.inl (Or.inr hg)))
    obtain ⟨h0, h1, h2⟩ := (lookupGatesT_iff δ b envV).mp hl
    exact ⟨(towerKept_iff δ b n e he _).mp ((keptT_reindex_iff δ n e b envV).mp hk),
      fun g hg => h g (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hg))))),
      fun g hg => h g (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_append.mp hg))))), h0, h1, h2,
      fun g hg => h g (Or.inl (Or.inr hg)), fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨hk, hs, ha, h0, h1, h2, hacc, hz⟩ g (((((hg | hg) | hg) | hg) | hg) | hg)
    · exact (keptT_reindex_iff δ n e b envV).mpr ((towerKept_iff δ b n e he _).mpr hk) g hg
    · exact hs g hg
    · exact ha g (List.mem_append.mpr hg)
    · exact (lookupGatesT_iff δ b envV).mpr ⟨h0, h1, h2⟩ g hg
    · exact hacc g hg
    · exact hz g hg

end GateIff

section Sat
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

set_option maxHeartbeats 4000000 in
/-- **`sat_iff` for the tower chip** (copy of `computeChipVCLQ7S_sat_iff`). -/
theorem computeChipVCLQ7T_sat_iff
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P ↔
      (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesQ7T n (MemoryTable.pwScaleExp K) b δ,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.compose P i).eval x =
        ((vclGatesQ7T n (MemoryTable.pwScaleExp K) b δ).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
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

/-- **Row semantics of acceptance**: a satisfied tower chip gives `TowerRowHolds` at every row. -/
theorem computeChipVCLQ7T_rowHolds
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P) :
    ∀ x ∈ rowNodeSet nodes, TowerRowHolds δ b n (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
  intro x hx
  exact (vclGatesQ7T_iff δ b n _ rfl _).mp
    (((computeChipVCLQ7T_sat_iff hn nodes b δ chalV pubVal orbit P).mp hsat).2 x hx)

/-- **Converse**: fixed preprocessing bound and `TowerRowHolds` at every row give satisfaction. -/
theorem computeChipVCLQ7T_of_rowHolds
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]
    (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).rap.w → F[X])
    (hb : (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit).BindsPreprocessing P)
    (hrow : ∀ x ∈ rowNodeSet nodes, TowerRowHolds δ b n (Reify.envOfTrace P orbit.ω x chalV pubVal)) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLQ7T hn nodes b δ chalV pubVal orbit) P :=
  (computeChipVCLQ7T_sat_iff hn nodes b δ chalV pubVal orbit P).mpr
    ⟨hb, fun x hx => (vclGatesQ7T_iff δ b n _ rfl _).mpr (hrow x hx)⟩

end Sat

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
