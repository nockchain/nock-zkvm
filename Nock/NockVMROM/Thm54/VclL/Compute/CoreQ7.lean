import Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7

/-!
# V4T5 : the `RowFacts` core at every node of the VCL `treeV` — `rowFactsAt`'s premise

.

* `HCFTree.treeV1` now reads the `ln`-patched rows (`envsP`); `RowAxQ7` re-proved at it (the patch
  moves no base column, no carrier and no `Dec`).
* **`treeV1_fst`** — the state/label projection of `treeV1` is the reconstruction over
  `TopoQ7.lblQ (cdOf …)`.
* **`rowFacts_core_Q7`** — at every node of `treeV`, the five carrier-free core facts (`pubSt`,
  `zRow` at `z = zQ` = compute slot 1, `vcomp`, `arity`, `link`) from `TopoQ7.q7_topology`
  (`Batch1111.rowFacts_core_ev`'s shape); **`rowFacts_Q7`** — the full `Batch1171.RowFacts` at
  `axB0Q7` with `RowAxQ7.rowFacts_Q7_of_core`.  The premises are coin events only (the `α`-root,
  prefix-`γ` and `α`-tiling events) plus acceptance: no trace premise.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace CoreQ7

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Reified Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.SVCompute
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.Framework

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. `InTree` through `mapNTree` -/

theorem inTree_mapNTree_eq {A B : Type} (f : A → B) (t : NTree A) (u : NTree B)
    (hu : InTree (mapNTree f t) u) : ∃ v, InTree t v ∧ u = mapNTree f v := by
  revert u
  let P := fun t : NTree A => ∀ u, InTree (mapNTree f t) u → ∃ v, InTree t v ∧ u = mapNTree f v
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih u hu
    simp only [mapNTree] at hu
    cases hu with
    | here => exact ⟨_, InTree.here _, by simp [mapNTree]⟩
    | sub hc hrec =>
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        obtain ⟨v, hv, hl⟩ := ih c0 hc0 u hrec
        exact ⟨v, InTree.sub hc0 hv, hl⟩
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem inTree_mapNTree_of {A B : Type} (f : A → B) (t v : NTree A) (hv : InTree t v) :
    InTree (mapNTree f t) (mapNTree f v) := by
  induction hv with
  | here c => exact InTree.here _
  | sub hs _ ih =>
      refine InTree.sub ?_ ih
      rw [mapNTree_children]
      exact List.mem_map_of_mem hs

/-! ## 2. The `ChipData` of a `VerifierData` and the tree's projection -/

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hC : ℕ} {S : MemShape}

/-- **The `ChipData` → `VerifierData` bridge**: the compute rows of `V` at coin / public vectors. -/
def cdOf (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) : ChipData F K hC :=
  ⟨V.N, V.hN, V.computeNodes, V.basis, V.orbitC, V.claim, pubVal, chalV⟩

/-- The generic datum of `cdOf V` (3-limb gather). -/
abbrev cdOfG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) : ChipDataG F K hC :=
  (cdOf V chalV pubVal).toG


section gen
variable {K' : Type} [Field K'] [Algebra F K'] [FiniteDimensional F K'] [Fintype K'] [DecidableEq K']
  [CharP K' (ringChar K')] (G : WalkQ7.CoordGather F K') {w : ℕ}

/-- **The generic chip datum of `V` at a gather** (`cdOfG V = cdOfGG (ofBasis V.basis) V`). -/
def cdOfGG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) : ChipDataG F K' hC :=
  ⟨V.N, V.hN, V.computeNodes, G, V.orbitC, V.claim, pubVal, chalV⟩

theorem cdOfG_eq_GG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) :
    cdOfG V chalV pubVal = cdOfGG (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal := rfl

set_option maxRecDepth 100000 in
/-- The `ChipData` row env is the `VerifierData` one (`rfl`). -/
theorem BV_cdOfGG (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) (r : Fin V.N) :
    BV (cdOfGG G V chalV pubVal) chalV pubVal Q r = envsVG G V chalV pubVal Q r := rfl

theorem lblQ_eq_at1G (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) (i : ℕ) :
    lblQ (cdOfGG G V chalV pubVal) chalV pubVal Q i = at1 V.hN (fun r => rowLabel (envsPG G V chalV pubVal Q r)) i := by
  unfold lblQ at1 envsPG rowOfG
  by_cases h : i - 1 < V.N
  · rw [dif_pos (show i - 1 < (cdOfGG G V chalV pubVal).N from h), dif_pos h]; rfl
  · rw [dif_neg (show ¬ i - 1 < (cdOfGG G V chalV pubVal).N from h), dif_neg h]; rfl

/-- The state/label projection of `treeV1` is the reconstruction over the patched labels. -/
theorem treeV1G_fst (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X]) :
    mapNTree Prod.fst (treeV1G G V chalV pubVal Q) =
      reconTree (fun i => fanoutComp (lblQ (cdOfGG G V chalV pubVal) chalV pubVal Q i).1)
        (lblQ (cdOfGG G V chalV pubVal) chalV pubVal Q) V.N := by
  unfold treeV1G computeTree treeOfRows
  rw [ReconTreeSize.mapNTree_reconTree]
  have h : ∀ i, lblQ (cdOfGG G V chalV pubVal) chalV pubVal Q i =
      (at1 V.hN (fun r => (rowLabel (envsPG G V chalV pubVal Q r)).1) i,
        at1 V.hN (fun r => (rowLabel (envsPG G V chalV pubVal Q r)).2) i) := by
    intro i; rw [lblQ_eq_at1G]; unfold at1
    by_cases hi : i - 1 < V.N
    · rw [dif_pos hi, dif_pos hi, dif_pos hi]
    · rw [dif_neg hi, dif_neg hi, dif_neg hi]
  rw [show lblQ (cdOfGG G V chalV pubVal) chalV pubVal Q = _ from funext h]

/-! ## 3. The core row facts -/

variable (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin w → F[X])
  (hadj : V.AdjacentC) (RF : RowFactsQ7 (cdOfGG G V chalV pubVal) chalV pubVal Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K') = 1 → n = 1)

include hadj RF hchar in
/-- **The `RowFacts` core at every node of `treeV`** (pubSt, zRow at `zQ`, vcomp, arity, link),
outside the `α`-root, prefix-`γ` and `α`-tiling events, given the frame's walk publics. -/
theorem rowFacts_core_Q7G {z : K'}
    (hinit : initQ (cdOfGG G V chalV pubVal) pubVal = alphaQ (cdOfGG G V chalV pubVal) chalV)
    (hseed : seedQ (cdOfGG G V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfGG G V chalV pubVal) chalV) (claimLabelVec z V.claim) *
        alphaQ (cdOfGG G V chalV pubVal) chalV)
    (hz : zQ (cdOfGG G V chalV pubVal) chalV ≠ 0)
    (hzi : G.chalSlot chalV 5 = (zQ (cdOfGG G V chalV pubVal) chalV)⁻¹)
    (hα : alphaQ (cdOfGG G V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
      (curW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (chldW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ (cdOfGG G V chalV pubVal) chalV) (claimLabelVec z V.claim)) V.N))
    (hγ : gammaQ (cdOfGG G V chalV pubVal) chalV ∉ prefixBadGammas
      (fun i => labelVecOfPub (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfGG G V chalV pubVal) i)))
      (fun i l => childVecN (pubAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfGG G V chalV pubVal) i))
        (tagsAt (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfGG G V chalV pubVal) i)) (l - 1))
      (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N)
    (htα : ¬ (alphaQ (cdOfGG G V chalV pubVal) chalV ^
        (1 + Sf (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
      alphaQ (cdOfGG G V chalV pubVal) chalV ^ V.N ∧
        1 + Sf (foW (cdOfGG G V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N)) :
    ∀ u, InTree (treeVG G V chalV pubVal Q) u →
      u.label.1.2.2.1.state = u.label.1.1 ∧ u.label.1.2.1.z = zQ (cdOfGG G V chalV pubVal) chalV ∧
      Vcomp u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2 ∧
      u.children.length = fanoutComp u.label.1.1 ∧
      ∀ (k : Fin 3) (c' : NTree ((State × DTcomp K') × ℕ)), u.children[(k : ℕ)]? = some c' →
        (c'.label.1.2.2.1.s, c'.label.1.2.2.1.f, c'.label.1.2.2.1.e) =
          sfTriple u.label.1.2.2.1 k := by
  intro u hu
  obtain ⟨hrvt, hlen3⟩ := q7_topology (cdOfGG G V chalV pubVal) chalV pubVal Q hadj RF hchar hinit hseed
    hz hzi hα hγ htα
  unfold treeVG at hu
  obtain ⟨v, hv, rfl⟩ := inTree_mapNTree_eq _ _ u hu
  have hw := inTree_mapNTree_of Prod.fst _ _ hv
  rw [treeV1G_fst] at hw
  have hF := ((RVT_iff_forall_InTree (Fcomp (K := K')) _).mp hrvt _ hw).1
  have hlen := hlen3 _ hw
  -- the node is a row label
  obtain ⟨j, hj⟩ := inTree_buildT_label _ _ _ 1 _ (by unfold reconTree at hw; exact hw)
  rw [mapNTree_label] at hF hj
  rw [mapNTree_children, List.length_map] at hlen
  have hcl : ∀ i : ℕ, (mapNTree Prod.fst v).childLabel i = v.children[i]?.map (fun c' => c'.label.1) := by
    intro i
    simp only [NTree.childLabel, NTree.childOpt, mapNTree_children, List.getElem?_map, Option.map_map]
    cases v.children[i]? <;> simp [mapNTree_label]
  obtain ⟨hst, hV, hiff, hlink⟩ := hF
  have key : ∀ i, i < 3 → (i < fanoutComp v.label.1.1 ↔ i < v.children.length) := by
    intro i hi
    have hi' := hiff ⟨i, hi⟩
    dsimp only at hi'
    rw [hcl i, ne_eq, Option.map_eq_none_iff, List.getElem?_eq_none_iff, not_le] at hi'
    exact hi'
  simp only [mapNTree_label, mapNTree_children, List.length_map]
  refine ⟨hst, ?_, hV, ?_, ?_⟩
  · -- zRow: the patched decode keeps slot 1
    rw [hj]
    exact (decodeInputs_z_lnPatch _).trans
      (SB_chal (cdOfGG G V chalV pubVal) chalV pubVal Q _ 1 (by norm_num))
  · have hfan : fanoutComp v.label.1.1 ≤ 3 := by cases v.label.1.1 <;> decide
    rcases Nat.lt_trichotomy v.children.length (fanoutComp v.label.1.1) with hlt | heq | hgt
    · exfalso; have := (key v.children.length (by omega)).1 hlt; omega
    · exact heq
    · exfalso; have := (key (fanoutComp v.label.1.1) (by omega)).2 hgt; omega
  · intro k c' hc
    rw [List.getElem?_map] at hc
    obtain ⟨c, hc0, rfl⟩ := Option.map_eq_some_iff.1 hc
    have hk : (k : ℕ) < fanoutComp v.label.1.1 := by
      rw [key k k.isLt]; exact (List.getElem?_eq_some_iff.1 hc0).1
    have hl := hlink k hk
    dsimp only at hl
    rw [hcl k, hc0] at hl
    simpa [mapNTree_label] using hl

end gen

set_option maxRecDepth 100000 in
/-- The `ChipData` row env is the `VerifierData` one (`rfl`). -/
theorem BV_cdOf (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) (r : Fin V.N) :
    BV (cdOfG V chalV pubVal) chalV pubVal Q r = envsV V chalV pubVal Q r := rfl

theorem lblQ_eq_at1 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) (i : ℕ) :
    lblQ (cdOfG V chalV pubVal) chalV pubVal Q i = at1 V.hN (fun r => rowLabel (envsP V chalV pubVal Q r)) i :=
  lblQ_eq_at1G (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q i

/-- The state/label projection of `treeV1` is the reconstruction over the patched labels. -/
theorem treeV1_fst (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X]) :
    mapNTree Prod.fst (treeV1 V chalV pubVal Q) =
      reconTree (fun i => fanoutComp (lblQ (cdOfG V chalV pubVal) chalV pubVal Q i).1)
        (lblQ (cdOfG V chalV pubVal) chalV pubVal Q) V.N :=
  treeV1G_fst (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q

variable (V : VerifierData F K hC S) (chalV pubVal : ℕ → F) (Q : Fin 232 → F[X])
  (hadj : V.AdjacentC) (RF : RowFactsQ7 (cdOfG V chalV pubVal) chalV pubVal Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

include hadj RF hchar in
/-- **The `RowFacts` core at every node of `treeV`** (pubSt, zRow at `zQ`, vcomp, arity, link),
outside the `α`-root, prefix-`γ` and `α`-tiling events, given the frame's walk publics. -/
theorem rowFacts_core_Q7 {z : K}
    (hinit : initQ (cdOfG V chalV pubVal) pubVal = alphaQ (cdOfG V chalV pubVal) chalV)
    (hseed : seedQ (cdOfG V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV) (claimLabelVec z V.claim) *
        alphaQ (cdOfG V chalV pubVal) chalV)
    (hz : zQ (cdOfG V chalV pubVal) chalV ≠ 0)
    (hzi : slotK V.basis chalV 5 = (zQ (cdOfG V chalV pubVal) chalV)⁻¹)
    (hα : alphaQ (cdOfG V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
      (curW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (chldW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV) (claimLabelVec z V.claim)) V.N))
    (hγ : gammaQ (cdOfG V chalV pubVal) chalV ∉ prefixBadGammas
      (fun i => labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
        (rowOfG (cdOfG V chalV pubVal) i)))
      (fun i l => childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfG V chalV pubVal) i))
        (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1))
      (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N)
    (htα : ¬ (alphaQ (cdOfG V chalV pubVal) chalV ^
        (1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
      alphaQ (cdOfG V chalV pubVal) chalV ^ V.N ∧
        1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N)) :
    ∀ u, InTree (treeV V chalV pubVal Q) u →
      u.label.1.2.2.1.state = u.label.1.1 ∧ u.label.1.2.1.z = zQ (cdOfG V chalV pubVal) chalV ∧
      Vcomp u.label.1.2.1 u.label.1.2.2.1 u.label.1.2.2.2 ∧
      u.children.length = fanoutComp u.label.1.1 ∧
      ∀ (k : Fin 3) (c' : NTree ((State × DTcomp K) × ℕ)), u.children[(k : ℕ)]? = some c' →
        (c'.label.1.2.2.1.s, c'.label.1.2.2.1.f, c'.label.1.2.2.1.e) =
          sfTriple u.label.1.2.2.1 k :=
  rowFacts_core_Q7G (WalkQ7.CoordGather.ofBasis V.basis) V chalV pubVal Q hadj RF hchar
    hinit hseed hz hzi hα hγ htα

/-- **`RowFacts` at `axB0Q7` at every node of `treeV`** (the frame's `rowFactsAt` body at the VCL
instance), from acceptance at the side chip `computeChipVCLQ7S`, injective adjacent nodes,
`N ≤ char`, and the three coin events (`α`-root, prefix-`γ`, `α`-tiling) at the frame's walk
publics.  `RowFactsQ7` is `RowFactsQ7.of_satS` of the acceptance. -/
theorem rowFacts_Q7 (γc ρc : ℕ) (hadj : V.AdjacentC) (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7S V.hN V.computeNodes V.basis γc ρc chalV pubVal V.orbitC) Q)
    (hNp : V.N ≤ ringChar K) {z : K}
    (hinit : initQ (cdOfG V chalV pubVal) pubVal = alphaQ (cdOfG V chalV pubVal) chalV)
    (hseed : seedQ (cdOfG V chalV pubVal) pubVal =
      Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV) (claimLabelVec z V.claim) *
        alphaQ (cdOfG V chalV pubVal) chalV)
    (hz : zQ (cdOfG V chalV pubVal) chalV ≠ 0)
    (hzi : slotK V.basis chalV 5 = (zQ (cdOfG V chalV pubVal) chalV)⁻¹)
    (hα : let RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
      alphaQ (cdOfG V chalV pubVal) chalV ∉ alphaBadOf (rootDiffP
        (curW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
        (chldW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
        (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar)
        (Walk.rlc (gammaQ (cdOfG V chalV pubVal) chalV) (claimLabelVec z V.claim)) V.N))
    (hγ : let RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
      gammaQ (cdOfG V chalV pubVal) chalV ∉ prefixBadGammas
        (fun i => labelVecOfPub (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
          (rowOfG (cdOfG V chalV pubVal) i)))
        (fun i l => childVecN (pubAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar
            (rowOfG (cdOfG V chalV pubVal) i))
          (tagsAt (cdOfG V chalV pubVal) chalV pubVal Q RF hchar (rowOfG (cdOfG V chalV pubVal) i)) (l - 1))
        (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N)
    (htα : let RF := RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat
      ¬ (alphaQ (cdOfG V chalV pubVal) chalV ^
          (1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N) =
        alphaQ (cdOfG V chalV pubVal) chalV ^ V.N ∧
          1 + Sf (foW (cdOfG V chalV pubVal) chalV pubVal Q RF hchar) V.N ≠ V.N)) :
    ∀ u, InTree (treeV V chalV pubVal Q) u →
      Nock.RedTeam.Batch1171.RowFacts (ax := axB0Q7 V (b0 (T := tableVCLE hC) Q))
        (zQ (cdOfG V chalV pubVal) chalV) (ringChar K) u := by
  intro u hu
  have hcore := rowFacts_core_Q7 V chalV pubVal Q hadj
    (RowFactsQ7.of_satS (cdOf V chalV pubVal) chalV pubVal Q γc ρc hinj hsat) hchar
    hinit hseed hz hzi hα hγ htα u hu
  exact rowFacts_Q7_of_core V γc ρc chalV pubVal Q hadj hinj hchar hsat hNp _ u hu hcore

end

end CoreQ7
end VclL.Compute
end Nock.NockVMROM.Thm54
