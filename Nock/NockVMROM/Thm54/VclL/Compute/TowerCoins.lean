import Nock.NockVMROM.Thm54.VclL.Compute.TowerBridge
import Nock.NockVMROM.Thm54.VclL.Compute.WalkSatQ7
import Nock.NockVMROM.Thm54.VclL.Chips.IOField

/-!
.

* `coinsQ_chalVQ7T`: at any environment whose challenges are `chalVQ7T δ b χ`, the `𝕂′` IO coins
  `coinsQ` of `TowerBridge` are `(ioSpecVCLQuad δ').ioCoins χ` (`γ′ = (χ4, χ6)`, `ρ′ = (χ5, χ7)`,
  `IOCoinSpec.ofExt`), the frame's coins.
* `seedVCLT`, `pubVQ7T`: the tower public map (`Re` seed at publics `3..5`, `Im` seed at `48..50`,
  every other public, in particular the `ρ` terminals `42..47` and the Im terminals `51..56`,
  read from the package publics).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.VclL.Chips
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. -/

/-- All 50 fingerprint roles
are coin round `1` at the 309 schedule (`newComputeRoleRound`), hence every Re FP column
`13 + 3 r + k` is round `1` (`newComputeColRound`), after the seed coins `χ2, χ3` (sampled after
block `0`, `seedSpecVCL.round0`).  The physical split `wRAP = ![208, 201]` is a different notion
(the RAP prefix, decoupled from the coin-round schedule exactly as at 309, where the same
columns lie in the first `208`). -/
theorem fpRole_round_one :
    ∀ r ∈ fpRoleList, RepartitionedStaging.newComputeRoleRound r = 1 := by decide

theorem fpCol_round_one :
    ∀ r ∈ fpRoleList, ∀ k < 3, RepartitionedStaging.newComputeColRound (13 + 3 * r + k) = 1 := by
  decide +kernel

/-- The Re FP columns lie in the first `208` columns and keep their 309 round under `vclCol`. -/
theorem fpCol_colRoundVCL :
    ∀ r ∈ fpRoleList, ∀ k < 3, colRoundVCL (13 + 3 * r + k) = 1 := by
  decide +kernel

/-- The seed coins are frame coins `2, 3`, sampled after block `0`. -/
theorem seed_coins_round_zero : frameVCL.sampledAfter ⟨2, by decide⟩ = 0 ∧
    frameVCL.sampledAfter ⟨3, by decide⟩ = 0 := by decide

/-! ## 2. The tower coins are the frame's coins -/

section Coins
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

theorem limbVal_chalVQ7T (χ : Coins frameVCL K) (q : ℕ) (hq : q < 16) :
    limbVal b (chalVQ7T δ b χ) (3 * q) = chalKQ7T δ χ q := by
  have hc : ∀ k : Fin 3, chalVQ7T δ b χ (3 * q + (k : ℕ)) = coord b (chalKQ7T δ χ q) k := by
    intro k
    have hk := k.isLt
    simp only [chalVQ7T, show 3 * q + (k : ℕ) < 48 by omega, ↓reduceIte]
    have hdiv : (3 * q + (k : ℕ)) / 3 = q := by omega
    have hmod : (3 * q + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    exact congrArg _ (Fin.ext hmod)
  unfold limbVal
  simp_rw [hc]
  exact reconstruct_coord b _

/-- **`coinsQ` at the tower challenge vector is the frame's `IOCoinSpec.ofExt` coin pair.** -/
theorem coinsQ_chalVQ7T (χ : Coins frameVCL K) (eF : Env F) (h : eF.chal = chalVQ7T δ b χ) :
    coinsQ δ (gatherEnv b eF) eF = (ioSpecVCLQuad (algebraMap F K δ)).ioCoins χ := by
  have e : ∀ q, q < 16 → (gatherEnv b eF).chal (3 * q) = chalKQ7T δ χ q := fun q hq => by
    simp only [gatherEnv, h]; exact limbVal_chalVQ7T δ b χ q hq
  rw [ioSpecVCLQuad_coins]
  have hg : (coinsQ δ (gatherEnv b eF) eF).gamma = Quad.mk _ (χ ⟨4, by decide⟩) (χ ⟨6, by decide⟩) := by
    rw [coinsQ_gamma]
    have h1 := e 7 (by norm_num)
    have h2 := e 14 (by norm_num)
    simp only [show 3 * 7 = 21 from rfl, show 3 * 14 = 42 from rfl] at h1 h2
    rw [h1, h2]; simp [chalKQ7T, chalKQ7]
  have hp : (coinsQ δ (gatherEnv b eF) eF).pole = Quad.mk _ (χ ⟨5, by decide⟩) (χ ⟨7, by decide⟩) := by
    rw [coinsQ_pole]
    have h1 := e 8 (by norm_num)
    have h2 := e 15 (by norm_num)
    simp only [show 3 * 8 = 24 from rfl, show 3 * 15 = 45 from rfl] at h1 h2
    rw [h1, h2]; simp [chalKQ7T, chalKQ7]
  cases hc : coinsQ δ (gatherEnv b eF) eF
  rw [hc] at hg hp
  simp only at hg hp
  rw [hg, hp]

end Coins

/-! ## 3. The public map at the tower -/

section Pubs
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

/-- **The `𝕂′` walk seed**: `RLC^{χ1}(claim label at z′) · χ0`, `z′ = (χ2, χ3)`, with the walk coins
`χ0, χ1` in `𝕂 ⊂ 𝕂′`. -/
def seedVCLT (claim : P8PublicClaim) (χ : Coins frameVCL K) : Quad (algebraMap F K δ) :=
  Walk.rlc (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨1, by decide⟩))
      (ComputeWalkSeed.claimLabelVec (zQuad δ χ) claim) *
    algebraMap K (Quad (algebraMap F K δ)) (χ ⟨0, by decide⟩)

/-- **The tower compute publics at `frameVCL` coins**: `initial_count = αC` at limbs `0..2`, the `Re`
walk seed at `3..5`, the `Im` walk seed at `48..50`, the package publics elsewhere (the `ρ`
terminals `42..47` and their Im halves `51..56` are the package's). -/
def pubVQ7T (claim : P8PublicClaim) (pkgPub : ℕ → F) (χ : Coins frameVCL K) : ℕ → F :=
  fun j =>
    if h0 : j < 3 then coord b (χ ⟨0, by decide⟩) ⟨j, h0⟩
    else if h : 3 ≤ j ∧ j < 6 then coord b (Quad.re _ (seedVCLT δ claim χ)) ⟨j - 3, by omega⟩
    else if h' : 48 ≤ j ∧ j < 51 then coord b (Quad.im _ (seedVCLT δ claim χ)) ⟨j - 48, by omega⟩
    else pkgPub j

theorem limbVal_pubVQ7T_zero (claim : P8PublicClaim) (pkgPub : ℕ → F) (χ : Coins frameVCL K) :
    limbVal b (pubVQ7T δ b claim pkgPub χ) 0 = χ ⟨0, by decide⟩ := by
  have hc : ∀ k : Fin 3, pubVQ7T δ b claim pkgPub χ (0 + (k : ℕ)) = coord b (χ ⟨0, by decide⟩) k := by
    intro k
    have hk : 0 + (k : ℕ) < 3 := by have := k.isLt; omega
    simp only [pubVQ7T, hk, ↓reduceDIte]
    exact congrArg _ (Fin.ext (by simp))
  unfold limbVal
  simp_rw [hc]
  exact reconstruct_coord b _

theorem limbVal_pubVQ7T_re (claim : P8PublicClaim) (pkgPub : ℕ → F) (χ : Coins frameVCL K) :
    limbVal b (pubVQ7T δ b claim pkgPub χ) 3 = Quad.re _ (seedVCLT δ claim χ) := by
  have hc : ∀ k : Fin 3, pubVQ7T δ b claim pkgPub χ (3 + (k : ℕ)) =
      coord b (Quad.re _ (seedVCLT δ claim χ)) k := by
    intro k
    have hk := k.isLt
    have h0 : ¬ (3 + (k : ℕ) < 3) := by omega
    have h1 : 3 ≤ 3 + (k : ℕ) ∧ 3 + (k : ℕ) < 6 := by omega
    simp only [pubVQ7T, h0, h1, ↓reduceDIte, and_self]
    exact congrArg _ (Fin.ext (by simp))
  unfold limbVal
  simp_rw [hc]
  exact reconstruct_coord b _

theorem limbVal_pubVQ7T_im (claim : P8PublicClaim) (pkgPub : ℕ → F) (χ : Coins frameVCL K) :
    limbVal b (pubVQ7T δ b claim pkgPub χ) 48 = Quad.im _ (seedVCLT δ claim χ) := by
  have hc : ∀ k : Fin 3, pubVQ7T δ b claim pkgPub χ (48 + (k : ℕ)) =
      coord b (Quad.im _ (seedVCLT δ claim χ)) k := by
    intro k
    have hk := k.isLt
    have h0 : ¬ (48 + (k : ℕ) < 3) := by omega
    have h1 : ¬ (3 ≤ 48 + (k : ℕ) ∧ 48 + (k : ℕ) < 6) := by omega
    have h2 : 48 ≤ 48 + (k : ℕ) ∧ 48 + (k : ℕ) < 51 := by omega
    simp only [pubVQ7T, h0, h1, h2, ↓reduceDIte, and_self]
    exact congrArg _ (Fin.ext (by simp))
  unfold limbVal
  simp_rw [hc]
  exact reconstruct_coord b _

/-- **The `𝕂′` walk seed public**: Re at `3..5`, Im at `48..50` give `seedVCLT`. -/
theorem seedQuad_pubVQ7T (claim : P8PublicClaim) (pkgPub : ℕ → F) (χ : Coins frameVCL K) :
    Quad.mk _ (limbVal b (pubVQ7T δ b claim pkgPub χ) 3) (limbVal b (pubVQ7T δ b claim pkgPub χ) 48) =
      seedVCLT δ claim χ := by
  rw [limbVal_pubVQ7T_re, limbVal_pubVQ7T_im, Quad.mk_re_im]

/-- The publics the package supplies (`42..47`, `51..56`, and everything `≥ 57`) are untouched. -/
theorem pubVQ7T_pkg (claim : P8PublicClaim) (pkgPub : ℕ → F) (χ : Coins frameVCL K) (j : ℕ)
    (h6 : 6 ≤ j) (h48 : j < 48 ∨ 51 ≤ j) : pubVQ7T δ b claim pkgPub χ j = pkgPub j := by
  have h0 : ¬ j < 3 := by omega
  have h1 : ¬ (3 ≤ j ∧ j < 6) := by omega
  have h2 : ¬ (48 ≤ j ∧ j < 51) := by omega
  simp [pubVQ7T, h0, h1, h2]

end Pubs

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
