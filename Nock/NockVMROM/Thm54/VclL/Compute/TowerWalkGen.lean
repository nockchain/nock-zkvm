import Nock.NockVMROM.Thm54.VclL.Compute.TowerWalkHonest
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderBinding
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestPlace

/-!
# The honest BFS walk of the generator (`HonestWalk` instance)

* `genWalkRoot`: the coin-set rendered AIR-ordered tree
  `mapNTree (setRowCoins a b c ∘ row ∘ renderNode z α) (bfsAssign (airReorder t))`, i.e. the carrier's
  committed compute tree (`genExactExecution_computeTree_eq`).
* `genWalk_htopo`: `HonestWalk.htopo` at every BFS row, from the generator's
  `assigned_airReorder_coins_binding` and the rendered state agreement.
* `genHonestWalk_exists`: an `HonestWalk` over `genWalkRoot` at any `(α, γ)` with `pubAt i` the BFS row's
  `Pub` and the seed `RLC^γ(label(row 0))·α`; with the root binding `hroot` (row 0's label is the claim's
  label at `z′`) its seed is `seedVCLT` (`seed_eq_seedVCLT`), i.e. `WalkRowEnv.pub0/pub1` at
  `eF.pub = pubCFT` (`towerEnv309_pub_placement`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.ComputeTable
open Nock.NockVMROM.Thm54.TraceGen

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

section GenWalk
variable {L : Type} [Field L]

/-- **The generator's walk tree** (the carrier's committed compute tree). -/
def genWalkRoot (z α a b c : L) (t : NTree (GenComputeRow L)) : NTree (State × DTcomp L) :=
  mapNTree ((setRowCoins a b c) ∘ GenComputeRow.row ∘ renderNode z α) (bfsAssign (airReorder t))

theorem renderNode_state_agree' (z α : L) (g : GenComputeRow L) :
    (renderNode z α g).row.1 = (renderNode z α g).row.2.2.1.state := by
  unfold renderNode
  cases g.skel.state <;> rfl

/-- **`HonestWalk.htopo` at every BFS row of the generated tree.** -/
theorem genWalk_htopo (z α a b c : L) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow L)} {result : Noun}
    (h : genComputeSkeleton (K := L) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ Walk.bfsForest [genWalkRoot z α a b c t],
      u.label.1 = u.label.2.2.1.state ∧ fanoutComp u.label.1 = u.children.length ∧
        childLinkComp u.label (fun j => u.childLabel j) := by
  intro u hu
  obtain ⟨h1, h2⟩ := assigned_airReorder_coins_binding (p := (t, result)) z α a b c h u hu
  refine ⟨?_, h1, h2⟩
  unfold genWalkRoot at hu
  rw [bfsForest_mapNTree_singleton, List.mem_map] at hu
  obtain ⟨w, -, rfl⟩ := hu
  rw [mapNTree_label]
  exact renderNode_state_agree' z α w.label

/-- The BFS row `Pub`s of a walk tree (row `0` = the root when out of range). -/
def bfsPubAt (root : NTree (State × DTcomp L)) (i : ℕ) : Pub L :=
  if h : i < (Walk.bfsForest [root]).length then ((Walk.bfsForest [root])[i]).label.2.2.1
  else root.label.2.2.1

/-- **The honest BFS walk of the generator** at any coins `(α, γ)`: root `genWalkRoot`, row `Pub`s
`bfsPubAt`, seed `RLC^γ(label(row 0))·α`.  No coin condition. -/
theorem genHonestWalk_exists (z αr a b c : L) (α γ : L) {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow L)} {result : Noun}
    (h : genComputeSkeleton (K := L) fuel subject formula = .ok (t, result)) :
    ∃ D : HonestWalk L, D.root = genWalkRoot z αr a b c t ∧ D.α = α ∧ D.γ = γ ∧
      D.seed = Walk.rlc γ (labelVecOfPub (bfsPubAt (genWalkRoot z αr a b c t) 0)) * α :=
  honestWalk_exists (genWalkRoot z αr a b c t) α γ _ (bfsPubAt (genWalkRoot z αr a b c t))
    (fun i hi => by simp [bfsPubAt, hi]) (genWalk_htopo z αr a b c h) rfl

/-- **The walk's row `Pub`s are the BFS rows'** (`D.hpub`, restated at the generator). -/
theorem genHonestWalk_pubAt (D : HonestWalk L) (i : ℕ) (hi : i < D.W.length) :
    D.pubAt i = bfsPubAt D.root i := by
  rw [← D.hpub i hi]; simp [bfsPubAt, hi]

/-- **The seed is the claim seed** under the root binding (row `0`'s label is the claim's): the walk
seed equals `RLC^γ(claimLabelVec z claim)·α`. -/
theorem genHonestWalk_seed_claim (D : HonestWalk L) (z : L) (claim : P8PublicClaim)
    (hroot : labelVecOfPub (D.pubAt 0) = ComputeWalkSeed.claimLabelVec z claim) :
    D.seed = Walk.rlc D.γ (ComputeWalkSeed.claimLabelVec z claim) * D.α := by
  rw [D.seed_eq, hroot]

end GenWalk

/-! ## `NextReads` assembled from the placement (item 2, partial) -/

section Next
open Nock.Reified Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.ComputeWalkLabel Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.T0Tower Nock.Framework Module Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework.Reify Nock.NockVMROM.Thm54.VclL.Chips
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable {δ : F} [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **`NextReads` at the honest tower env, from its two content fields.**  The selector, `α` and `γ`
fields are discharged by the next-row base placement (`hFn`, next row one-hot at `D.pubAt j`) and the
challenge placement (`hch`, walk coins `χ₀ / χ₁`); the restored-source field `hsrc` and the hosted
child-tag field `htag` are the remaining content (not discharged here). -/
theorem nextReads_of_fill (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)
    (D : HonestWalk (Quad (algebraMap F K δ))) (j : ℕ) (v' : TowerRowVals (K := K) δ) (eF : Env F)
    (hFn : ∀ c, SrcRead c → eF.traceNext c = srcColT b v' c) (hch : eF.chal = chalVQ7T δ b χ)
    (hsel : ∀ st : State, v'.base ⟨Nock.Reified.opCol st, by
        have := opCol_eq_stateIndex st; have := (stateIndex st).isLt; omega⟩ =
      if st = (D.pubAt j).state then 1 else 0)
    (hα : D.α = algebraMap K _ (χ ⟨0, by decide⟩)) (hγ : D.γ = algebraMap K _ (χ ⟨1, by decide⟩))
    (hsrc : ∀ (role c : ℕ) (hr : role < 12) (hc : c < 3),
      (sourcePubAtR curReader (D.pubAt j).state role c).eval
          (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv) =
        fpCoordinate (pubFingerprint (D.pubAt j) ⟨role, hr⟩) ⟨c, hc⟩)
    (htag : ∀ k : Fin 3, (childTagHost curReader (D.pubAt j).state k).eval
          (shiftNext (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv) =
        childStateTagCol D.W (j + 1) k) :
    NextReads D (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv j := by
  have hchal := towerEnv309_chal_placement δ b χ eF hch
  refine ⟨?_, hsrc, htag, ?_, ?_⟩
  · intro st
    have hlt : Nock.Reified.opCol st < 11 := by
      rw [opCol_eq_stateIndex]; exact (stateIndex st).isLt
    have a1 : Nock.Reified.opCol st ≠ 303 := by omega
    have a2 : Nock.Reified.opCol st ≠ 306 := by omega
    simp only [Env309.toSourceEnv, a1, a2, if_false, CorrectedFinalTypedEnv.toSourceEnv,
      show Nock.Reified.opCol st < 13 by omega, dif_pos]
    rw [towerEnv309_baseNext_of_src b v' eF hFn, hsel]
    split_ifs <;> simp
  · show (walkChallenge 0).eval (towerEnv309 δ towerM (gatherEnv b eF) eF).toSourceEnv = D.α
    rw [hα, ← hchal.2.2.2.2.2.1]
    simp [walkChallenge, walkChallengeBase, Expr.eval, Env309.toSourceEnv,
      CorrectedFinalTypedEnv.toSourceEnv]
  · rw [hγ, ← hchal.2.2.2.2.2.2]
    simp [walkGammaChallenge, ComputeWalkLabel.walkGammaChallengeIndex, Expr.eval, Env309.toSourceEnv,
      CorrectedFinalTypedEnv.toSourceEnv]

end Next

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
