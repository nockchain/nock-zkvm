import Nock.NockVMROM.Thm54.VclL.Compute.WalkRows
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChipLayoutP

/-!
# V4c item 1 (layout half): `layoutVCLD`, the repaired chip as a `ChipLayoutP`

* `layoutVCLD_sat_iff` is the `sat_iff` field: acceptance ⇔ bound preprocessing and, at every row,
  the VCL obligations and every gate of `vclGatesD`.
* `layoutVCLD_gatesOK`: the shared gate families (base and kept core, reindexed; the arity-1
  serial) are gates of the chip.
* **`rowFactsP_vcomp`**: from `RowFactsP D (layoutVCLD γc ρc) c Q` (which `RowFactsP.of_sat` gives
  from acceptance), every row is `V_comp` at the fingerprints it decodes; **`rowFactsP_transition`**
  and **`rowFactsP_queue`**: the walk / queue sources at VCL semantics, through the layout.

The R2 twins stated over `CorrectedComputeSourceObligations` do NOT transfer to this layout by
`hL`: their walk reads the 303-HOSTED overlay; the VCL walk lives in `W0`/`W1`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.SVCompute
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler

set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] {h : ℕ}

/-- The shared gate families of the repaired chip (base and kept core reindexed — identity on
columns `< 202` — and the arity-1 serial; no accumulator family: VCL's IO accumulators are the
lookup slots, left parametric). -/
def gatesVCLD (D : ChipData F K h) : SharedGateSet F where
  base := (finalBaseTransitionGates (F := F) D.N).map reindexE
  walk := (correctedCoreVCL D.basis).map reindexE
  acc := []
  serial := serialGates

/-- The VCL obligations at a row (the gathered typed environment is not read; the 309-shaped
pull-back of the raw row is). -/
def oblVCLD (D : ChipData F K h) (_env : CorrectedFinalTypedEnv F K) (envF : Env F) : Prop :=
  VclSourceObligations D.N (gather309 D.basis (pullEnv envF)) (pullEnv envF)

theorem layoutVCLD_sat_iff (γc ρc : ℕ) (D : ChipData F K h)
    (c : OptimizedProductionChallengeTuple K F)
    (Q : Fin (computeChipVCLD D.hN D.nodes D.basis γc ρc (computeChalValOfTuple D.basis c)
      (computePublicOfTuple D.basis D.claim D.pub c) D.orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLD D.hN D.nodes D.basis γc ρc
        (computeChalValOfTuple D.basis c) (computePublicOfTuple D.basis D.claim D.pub c) D.orbit) Q ↔
      ((computeChipVCLD D.hN D.nodes D.basis γc ρc (computeChalValOfTuple D.basis c)
          (computePublicOfTuple D.basis D.claim D.pub c) D.orbit).BindsPreprocessing Q ∧
        ∀ x ∈ rowNodeSet D.nodes,
          oblVCLD D
            (gatherCorrectedFinalTypedEnv D.basis
              (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
                (computePublicOfTuple D.basis D.claim D.pub c)))
            (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
              (computePublicOfTuple D.basis D.claim D.pub c)) ∧
          ∀ g ∈ vclGatesD D.N D.basis γc ρc,
            g.eval (envOfTrace Q D.orbit.ω x (computeChalValOfTuple D.basis c)
              (computePublicOfTuple D.basis D.claim D.pub c)) = 0) := by
  rw [computeChipVCLD_sat_iff]
  constructor
  · rintro ⟨hb, hall⟩
    refine ⟨hb, fun x hx => ⟨?_, hall x hx⟩⟩
    exact VclSourceObligations.of_vclGates D.N D.basis _ (fun g hg => hall x hx g (by
      simp only [vclGatesD, vclGatesA, List.mem_append]; exact Or.inl (Or.inl hg)))
  · rintro ⟨hb, hall⟩
    exact ⟨hb, fun x hx => (hall x hx).2⟩

/-- **`layoutVCLD`: the repaired chip as a `ChipLayoutP`.** -/
def layoutVCLD (γc ρc : ℕ) : ChipLayoutP F K h where
  w := vclWidthD
  colRound := fun j => colRoundVCLD j
  base := by simp [vclWidthD]
  role := fun r => 13 + 3 * r
  role_eq := fun _ => rfl
  nRoles := 63
  roles_fit := by simp [vclWidthD]
  serial := ⟨serialCol, by simp [serialCol, vclWidthD]⟩
  serial_round0 := by decide
  gates := gatesVCLD
  allGates := fun D => vclGatesD D.N D.basis γc ρc
  build := fun D c => computeChipVCLD D.hN D.nodes D.basis γc ρc
    (computeChalValOfTuple D.basis c) (computePublicOfTuple D.basis D.claim D.pub c) D.orbit
  build_w := fun _ _ => rfl
  Obl := oblVCLD
  sat_iff := fun D c Q => layoutVCLD_sat_iff γc ρc D c Q
  masks_of_bind := by
    intro D c Q hb h11 h12
    have h0 := hb ⟨0, by change 0 < 2; norm_num⟩
    have h1 := hb ⟨1, by change 1 < 2; norm_num⟩
    exact ⟨h0, h1⟩

/-- **The shared families are gates of the chip** (the `hL` premise). -/
theorem layoutVCLD_gatesOK (γc ρc : ℕ) (D : ChipData F K h) :
    (layoutVCLD (F := F) (K := K) (h := h) γc ρc).GatesOK D := by
  intro g hg
  simp only [layoutVCLD, gatesVCLD, SharedGateSet.toList, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false] at hg ⊢
  simp only [vclGatesD, vclGatesA, vclGates, List.mem_append, List.mem_map]
  rcases hg with ((⟨g', hg', rfl⟩ | ⟨g', hg', rfl⟩) | hs)
  · exact Or.inl (Or.inl (Or.inl ⟨g', by simp only [keptGates309, List.mem_append]; tauto, rfl⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨g', by simp only [keptGates309, List.mem_append]; tauto, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr hs))

variable [CharP K (ringChar K)]

/-- **The row facts at `layoutVCLD` give `V_comp` on every row.** -/
theorem rowFactsP_vcomp (γc ρc : ℕ) (D : ChipData F K h)
    (c : OptimizedProductionChallengeTuple K F)
    (Q : Fin (chipOfP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c).rap.w → F[X])
    (RF : RowFactsP D (layoutVCLD γc ρc) c Q)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) (i : Fin D.N)
    (hzZ : (zZinvExpr.subst computeSubst).eval
      (gatherCorrectedFinalTypedEnv D.basis (pullEnv (envFAtD D c Q i))).toSourceEnv = 0) :
    VcompAt (gatherCorrectedFinalTypedEnv D.basis (pullEnv (envFAtD D c Q i))) :=
  vcl_obligations_vcomp D.N D.basis _ (RF.obl i) hchar hzZ

/-- **The walk / queue sources through the layout**: nonterminal rows have the VCL decoded
transition sources; every row has the queue witness. -/
theorem rowFactsP_transition (γc ρc : ℕ) (D : ChipData F K h)
    (c : OptimizedProductionChallengeTuple K F)
    (Q : Fin (chipOfP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c).rap.w → F[X])
    (RF : RowFactsP D (layoutVCLD γc ρc) c Q) (i : Fin D.N) (hi : (i : ℕ) ≠ D.N - 1) :
    DecodedTransitionSourcesVCL (gather309 D.basis (pullEnv (envFAtD D c Q i))) := by
  refine conditional_transition_soundness_vcl (RF.obl i) ?_
  change (pullEnv (envFAtD D c Q i)).trace 12 = 0
  rw [pullEnv_trace_lt _ 12 (by norm_num)]
  have hm := (RF.masks i).2
  simp only [hi, if_false] at hm
  exact hm

theorem rowFactsP_queue (γc ρc : ℕ) (D : ChipData F K h)
    (c : OptimizedProductionChallengeTuple K F)
    (Q : Fin (chipOfP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c).rap.w → F[X])
    (RF : RowFactsP D (layoutVCLD γc ρc) c Q) (i : Fin D.N) :
    queueNonEmpty309.eval (gather309 D.basis (pullEnv (envFAtD D c Q i))) = 0 ∧
      queueTiling309.eval (gather309 D.basis (pullEnv (envFAtD D c Q i))) = 0 :=
  queue_sources_vcl (RF.obl i)

end

end VclL.Compute
end Nock.NockVMROM.Thm54
