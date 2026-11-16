/-
  Nock/NockVMROM/Thm54/P8Core/SVCompute/ChipLayoutP.lean

  **The obligations-parametric layout `ChipLayoutP`.**

  R2's `ChipLayout.sat_iff` is stated over `CorrectedComputeSourceObligations`, whose fields include
  Form R (`formR99`, `formRLam`, the core ids `79`/`80` inside `extensionCore21`) and the arity-form
  carrier (`expGates`).  For `computeChipVCL`  that predicate is FALSE: the chip commits none
  of those gates.  `ChipLayoutP` is `ChipLayout` with the obligations predicate a FIELD (`Obl`, read at
  a datum, the gathered typed row environment and the raw row environment), so a chip states its own
  source language.  `ChipLayout.toP` is the embedding (`Obl := CorrectedComputeSourceObligations`);
  `layout309P := layout309.toP`; `RowFactsP` / `RowFactsP.of_sat` are `RowFacts` / `RowFacts.of_sat`
  at the field; `rowFacts_iff_toP` is the one-line bridge, so every R2 twin stated over
  `RowFacts D L c Q` is a twin over `RowFactsP D L.toP c Q`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChipData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler

noncomputable section

section LayoutP

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}

/-- **`ChipLayout` with the obligations predicate a field.**  Every field of R2's `ChipLayout`, with
`sat_iff` stated over `Obl D` (the chip's own gathered source language) in place of the fixed
`CorrectedComputeSourceObligations D.N`. -/
structure ChipLayoutP (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] (h : ℕ) where
  w : ℕ
  colRound : Fin w → ℕ
  base : 13 ≤ w
  role : ℕ → ℕ
  role_eq : ∀ r, role r = 13 + 3 * r
  nRoles : ℕ
  roles_fit : 13 + 3 * nRoles ≤ w
  serial : Fin w
  serial_round0 : colRound serial = 0
  gates : ChipData F K h → SharedGateSet F
  allGates : ChipData F K h → List (CoeffExpr F)
  build : ChipData F K h → OptimizedProductionChallengeTuple K F → FixedPreprocessingRAP F
  build_w : ∀ D c, (build D c).rap.w = w
  /-- The chip's gathered source language at one row: a predicate of the datum, the gathered typed
  environment and the raw environment. -/
  Obl : ChipData F K h → CorrectedFinalTypedEnv F K → Env F → Prop
  sat_iff : ∀ (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
      (Q : Fin (build D c).rap.w → F[X]),
    RAP.SatisfiesWithPreprocessing (build D c) Q ↔
      ((build D c).BindsPreprocessing Q ∧
        ∀ x ∈ rowNodeSet D.nodes,
          Obl D
            (gatherCorrectedFinalTypedEnv D.basis
              (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
                (computePublicOfTuple D.basis D.claim D.pub c)))
            (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
              (computePublicOfTuple D.basis D.claim D.pub c)) ∧
          ∀ g ∈ allGates D,
            g.eval (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
              (computePublicOfTuple D.basis D.claim D.pub c)) = 0)
  masks_of_bind : ∀ (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F)
      (Q : Fin (build D c).rap.w → F[X]), (build D c).BindsPreprocessing Q →
    ∀ (h11 : 11 < (build D c).rap.w) (h12 : 12 < (build D c).rap.w),
      Q ⟨11, h11⟩ = firstRowMask D.nodes ∧ Q ⟨12, h12⟩ = lastRowMask D.hN D.nodes

/-- **The embedding**: R2's layout is the `ChipLayoutP` at `Obl := CorrectedComputeSourceObligations`. -/
def ChipLayout.toP (L : ChipLayout F K h) : ChipLayoutP F K h where
  w := L.w
  colRound := L.colRound
  base := L.base
  role := L.role
  role_eq := L.role_eq
  nRoles := L.nRoles
  roles_fit := L.roles_fit
  serial := L.serial
  serial_round0 := L.serial_round0
  gates := L.gates
  allGates := L.allGates
  build := L.build
  build_w := L.build_w
  Obl := fun D => CorrectedComputeSourceObligations D.N
  sat_iff := L.sat_iff
  masks_of_bind := L.masks_of_bind

/-- The chip of a datum at a `ChipLayoutP`. -/
def chipOfP (D : ChipData F K h) (L : ChipLayoutP F K h)
    (c : OptimizedProductionChallengeTuple K F) : FixedPreprocessingRAP F :=
  L.build D c

theorem chipOfP_w (D : ChipData F K h) (L : ChipLayoutP F K h)
    (c : OptimizedProductionChallengeTuple K F) : (chipOfP D L c).rap.w = L.w :=
  L.build_w D c

/-- The chip is unchanged by the embedding (`rfl`). -/
theorem chipOfP_toP (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) : chipOfP D L.toP c = chipOf D L c := rfl

/-- `L.gates ⊆ (chipOfP D L c).gates` at a `ChipLayoutP` (the `hL` premise). -/
def ChipLayoutP.GatesOK (L : ChipLayoutP F K h) (D : ChipData F K h) : Prop :=
  ∀ g ∈ (L.gates D).toList, g ∈ L.allGates D

theorem gatesOK_toP (L : ChipLayout F K h) (D : ChipData F K h) :
    L.toP.GatesOK D ↔ L.GatesOK D := Iff.rfl

/-- **`layout309P`**: the live package chip's layout, at its existing obligations. -/
def layout309P : ChipLayoutP F K h := (layout309 (F := F) (K := K) (h := h)).toP

/-- The bridge: `layout309P`'s obligations are R2's (`rfl`). -/
theorem layout309P_Obl (D : ChipData F K h) :
    (layout309P (F := F) (K := K) (h := h)).Obl D = CorrectedComputeSourceObligations D.N := rfl

theorem layout309P_build (D : ChipData F K h) (c : OptimizedProductionChallengeTuple K F) :
    (layout309P (F := F) (K := K) (h := h)).build D c = (layout309 (F := F) (K := K) (h := h)).build D c :=
  rfl

theorem layout309P_gatesOK (D : ChipData F K h) : (layout309P (F := F) (K := K) (h := h)).GatesOK D :=
  layout309_gatesOK D

/-- **The row facts at a `ChipLayoutP`**: the chip's own obligations, every listed gate, the masks. -/
structure RowFactsP (D : ChipData F K h) (L : ChipLayoutP F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOfP D L c).rap.w → F[X]) : Prop where
  obl : ∀ i : Fin D.N, L.Obl D (rowEnvAtD D c Q i) (envFAtD D c Q i)
  gates : ∀ i : Fin D.N, ∀ g ∈ L.allGates D, g.eval (envFAtD D c Q i) = 0
  masks : ∀ i : Fin D.N,
    (rowEnvAtD D c Q i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
    (rowEnvAtD D c Q i).baseTrace 12 = (if (i : ℕ) = D.N - 1 then 1 else 0)

/-- **Acceptance gives the row facts** at any `ChipLayoutP` (R2's `RowFacts.of_sat`, at the field). -/
theorem RowFactsP.of_sat (D : ChipData F K h) (L : ChipLayoutP F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOfP D L c).rap.w → F[X])
    (hinj : D.Injective) (hsat : RAP.SatisfiesWithPreprocessing (chipOfP D L c) Q) :
    RowFactsP D L c Q := by
  have hs := (L.sat_iff D c Q).1 hsat
  have hw : 12 < (chipOfP D L c).rap.w := by
    rw [chipOfP_w]; have := L.base; omega
  have hw11 : 11 < (chipOfP D L c).rap.w := by omega
  obtain ⟨m0, m1⟩ := L.masks_of_bind D c Q hs.1 hw11 hw
  have hmem : ∀ i : Fin D.N, D.nodes i ∈ rowNodeSet D.nodes := fun i => by simp [rowNodeSet]
  refine ⟨fun i => (hs.2 _ (hmem i)).1, fun i => (hs.2 _ (hmem i)).2, fun i => ⟨?_, ?_⟩⟩
  · show (envOfTrace Q D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c)).trace 11 = _
    simp only [envOfTrace, dif_pos hw11]
    rw [show Q ⟨11, hw11⟩ = firstRowMask D.nodes from m0, Nock.Framework.firstRowMask_eval _ hinj]
  · show (envOfTrace Q D.orbit.ω (D.nodes i) (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c)).trace 12 = _
    simp only [envOfTrace, dif_pos hw]
    rw [show Q ⟨12, hw⟩ = lastRowMask D.hN D.nodes from m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]

/-- **The one-line bridge**: R2's row facts at a layout are the `ChipLayoutP` row facts at its
embedding, so every twin over `RowFacts D L c Q` reads `RowFactsP D L.toP c Q`. -/
theorem rowFacts_iff_toP (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X]) :
    RowFacts D L c Q ↔ RowFactsP D L.toP c Q :=
  ⟨fun hR => ⟨hR.obl, hR.gates, hR.masks⟩, fun hR => ⟨hR.obl, hR.gates, hR.masks⟩⟩

/-- `RowFactsP.of_sat` at the embedding is R2's `RowFacts.of_sat` (through the bridge). -/
theorem rowFacts_of_satP (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X])
    (hinj : D.Injective) (hsat : RAP.SatisfiesWithPreprocessing (chipOf D L c) Q) :
    RowFacts D L c Q :=
  (rowFacts_iff_toP D L c Q).2 (RowFactsP.of_sat D L.toP c Q hinj hsat)

end LayoutP

/-! Each pair is `(twin module, CorrectedComputeSourceObligations fields read through RF.obl)`.  A
`ChipLayoutP` instance makes a twin family available through `hL` iff its `Obl` yields those fields
at `rowEnvAtD` / `envFAtD`.  `formR99`, `formRLam` and `expGates` are read by NO twin; the core ids
`79`/`80` (Form R) are read by no twin either (`extensionCore21` is read at `packedQueueNonEmptyId`,
`packedQueueTilingId`, `packedWalkLnId`, `packedWalkCountId`, `packedWalkAccId`, `packedChainId`). -/
def sharedOblFields : List (String × List String) :=
  [("ChainTwins", ["base15", "extensionCore21 packedChainId", "residualAux3 2",
      "endpointDegreeTwo2", "ln_chain / ln_recurrence (whole structure)"]),
   ("WalkTwins", ["selectorEquality2", "endpointDegreeTwo2", "endpointDegreeFour1",
      "extensionCore21 packedWalkLnId / packedWalkCountId / packedWalkAccId", "residualAux3 0 / 1"]),
   ("QueueTwins", ["extensionCore21 packedQueueNonEmptyId / packedQueueTilingId"]),
   ("RootTwins / EnvTwins / IndexTwins", ["via WalkTwins / ChainTwins"])]

end

end Nock.NockVMROM.Thm54.SVCompute
