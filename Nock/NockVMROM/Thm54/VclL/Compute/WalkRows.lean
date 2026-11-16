import Nock.NockVMROM.Thm54.VclL.Compute.RowDecode

/-!
# V4c items 5–6 (row level): the walk / queue sources at VCL semantics

The R2 walk / queue twins (`P8Core/SVCompute/WalkTwins.lean`, `QueueTwins.lean`) read the walk at
the 303-HOSTED semantics (count / accumulator in the residual roles `58`/`59`, queue at core
`76`/`77` on the hosted overlay) through `CorrectedComputeSourceObligations` (Form R included).  At
`computeChipVCLD` the walk lives in the dedicated columns `W0`/`W1` (VCL `208..213`, the 309
semantics: core `76`/`77` are `queueNonEmpty309` / `queueTiling309`, aux `0`/`1` pin the residual
roles to `walkCountStep309` / `walkAccStep309`).  This module is the per-row twin of
`conditional_transition_soundness309` at the VCL obligations:

* `ext_gate_zero_vcl` — every untouched kept core position vanishes on a nonterminal row;
* **`conditional_transition_soundness_vcl`** — on a nonterminal row with the VCL obligations,
  the 76 core coin-free sources at 309 semantics (`paperPackingCoreGates309`: the packed table,
  the always-on block, `lnChain`, `walkLn`, and the two walk recurrences on `W0`/`W1`) vanish,
  and so do the two sampled-IO sources VCL keeps (positions `78`, `81`; `79`/`80` are the Form R
  denominator pins it drops);
* **`queue_sources_vcl`** — the queue witness gates `queueNonEmpty309`, `queueTiling309` vanish
  on EVERY row;
* `decoded309_toVCL` — positive control: the 309 decode implies the VCL one;
* at the chip: `computeChipVCLD_transition_sources`, `computeChipVCLD_queue_sources`.

Not done here (recorded): the global `WalkSat` assembly over all rows at `W0`/`W1` (the twin of
`deployed_walkSatD`), and from it `BFSValid` / tiling (`deployed_bfsValidD`, `deployed_tilingD`).

Paper: the paper (the walk accumulator identity), `:1906`, `:2263`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal hiding residualWitnessRole ResidualWitnessId FinalExtensionColumn
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open scoped Polynomial

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

noncomputable section

section rows
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem mem_keptCoreIds (i : CorrectedCoreExtGateId) (h79 : i.val ≠ 79) (h80 : i.val ≠ 80) :
    i ∈ keptCoreIds := by
  simp only [keptCoreIds, List.mem_filter, List.mem_finRange, true_and, formRCoreIds]
  simp [h79, h80]

/-- Every untouched kept core position vanishes on a nonterminal row (`ext_gate_zero309` at the
VCL obligations). -/
theorem ext_gate_zero_vcl {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligations n env envF) (hnotLast : env.base.baseTrace 12 = 0)
    (i : CorrectedCoreExtGateId) (hi : i ∈ keptCoreIds)
    (h74 : i ≠ packedWalkCountId) (h75 : i ≠ packedWalkAccId)
    (h76 : i ≠ packedQueueNonEmptyId) (h77 : i ≠ packedQueueTilingId) :
    (correctedFinalExtGate i).eval env.base = 0 := by
  have hc := hsource.extensionCore i hi
  simp only [coreSemValue309, h76, h77, if_false] at hc
  by_cases h20 : i = packedChainId
  · subst i
    have ha := hsource.residualAux 2
    simp only [auxSemValue309, correctedAuxSemanticValue] at ha
    have hchain : env.base.extTrace 60 = env.base.extTraceNext 32 := by
      simpa [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, accAfterChain,
        CorrectedFinalTypedExpr.eval, hnotLast, sub_eq_zero] using hc
    rw [← correctedAccAfterStep_eval_eq_fold env.base hchain]
    exact ha
  by_cases h89 : i = packedLnChainId ∨ i = packedWalkLnId
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h74, h75, h20, h89, ↓reduceIte, notLastScalar, hnotLast, sub_zero, map_one,
      one_mul] at hc
    exact hc
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h74, h75, h20, h89, ↓reduceIte] at hc
    exact hc

/-- **The decoded transition sources at VCL semantics**: the 76 core coin-free sources at 309
(walk on `W0`/`W1`) and the two sampled-IO sources VCL keeps. -/
structure DecodedTransitionSourcesVCL (env : Env309 F K) : Prop where
  nonIO : ∀ e ∈ paperPackingCoreGates309, e.eval env.toSourceEnv = 0
  sampledIOKept : ∀ (j : ℕ) (hj : j < finalSampledIOTransitionGates.length), j ≠ 1 → j ≠ 2 →
    (finalSampledIOTransitionGates[j]'hj).eval env.toSourceEnv = 0

/-- Positive control: the 309 decode implies the VCL one. -/
theorem decoded309_toVCL {env : Env309 F K} (h : DecodedTransitionSources309 env) :
    DecodedTransitionSourcesVCL env :=
  ⟨h.nonIO, fun j hj _ _ => h.sampledIOSafe4 _ (List.getElem_mem hj)⟩

/-- **`conditional_row_decode` at VCL semantics.** -/
theorem conditional_transition_soundness_vcl {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligations n env envF) (hnotLast : env.base.baseTrace 12 = 0) :
    DecodedTransitionSourcesVCL env := by
  have hpos : ∀ (i : ℕ) (hi : i < 82), i ≠ 74 → i ≠ 75 → i ≠ 76 → i ≠ 77 → i ≠ 79 → i ≠ 80 →
      (finalExtTransitionGates.get ⟨i, by simpa using hi⟩).eval env.toSourceEnv = 0 := by
    intro i hi h74 h75 h76 h77 h79 h80
    rw [eval_toSourceEnv309_of_noWalkVars env _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
    have := correctedFinalExtGate_eval_source env.base ⟨i, hi⟩
    simp only at this
    rw [this]
    exact ext_gate_zero_vcl hsource hnotLast ⟨i, hi⟩ (mem_keptCoreIds _ h79 h80)
      (fun h => h74 (congrArg Fin.val h)) (fun h => h75 (congrArg Fin.val h))
      (fun h => h76 (congrArg Fin.val h)) (fun h => h77 (congrArg Fin.val h))
  have hmem : ∀ e, (∃ (i : ℕ) (hi : i < 82), i ≠ 74 ∧ i ≠ 75 ∧ i ≠ 76 ∧ i ≠ 77 ∧ i ≠ 79 ∧
      i ≠ 80 ∧ finalExtTransitionGates.get ⟨i, by simpa using hi⟩ = e) →
      e.eval env.toSourceEnv = 0 := by
    rintro e ⟨i, hi, h74, h75, h76, h77, h79, h80, rfl⟩
    exact hpos i hi h74 h75 h76 h77 h79 h80
  have hres : ∀ j : Fin 2, (residualSource309 j).eval env = 0 := by
    intro j
    have hj2 : (⟨j.val, by omega⟩ : CorrectedResidualWitnessId) ≠ 2 := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have ha := hsource.residualAux ⟨j.val, by omega⟩
    have hidx : aux309Idx ⟨j.val, by omega⟩ hj2 = j := Fin.ext rfl
    simp only [auxSemValue309, dif_neg hj2, hidx, sub_eq_zero] at ha
    fin_cases j
    · have hc := hsource.extensionCore packedWalkCountId
        (mem_keptCoreIds _ (by decide) (by decide))
      simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnotLast,
        packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] at hc
      rw [← ha]
      simpa [residualWitnessRole] using hc
    · have hc := hsource.extensionCore packedWalkAccId
        (mem_keptCoreIds _ (by decide) (by decide))
      simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnotLast,
        packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] at hc
      rw [← ha]
      simpa [residualWitnessRole] using hc
  have hcount : walkCountStep309.eval env.toSourceEnv = 0 := by
    rw [lower309_eval env _ _ (lower309_some _ lower309_total.1)]
    exact hres 0
  have hacc : walkAccStep309.eval env.toSourceEnv = 0 := by
    rw [lower309_eval env _ _ (lower309_some _ lower309_total.2.1)]
    exact hres 1
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [paperPackingCoreGates309, List.mem_append] at he
    have hpl : packedTableOptimized.length = 66 := by decide
    have hlen : alwaysOnOptimized.length = 6 := by decide
    rcases he with (hrow | hon) | hcr
    · obtain ⟨i, hget⟩ := List.mem_iff_get.mp hrow
      have hi : i.val < 66 := by have := i.isLt; omega
      apply hmem e
      refine ⟨i.val, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
      rw [← hget]
      simp only [List.get_eq_getElem, finalExtTransitionGates_split, List.append_assoc]
      rw [List.getElem_append_left (by omega)]
    · obtain ⟨i, hget⟩ := List.mem_iff_get.mp hon
      have hi : i.val < 6 := by have := i.isLt; omega
      apply hmem e
      refine ⟨66 + i.val, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
      rw [← hget]
      simp only [List.get_eq_getElem, finalExtTransitionGates_split, List.append_assoc]
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
      simp [hpl]
    · simp only [crossRowSingletons309, List.mem_cons, List.not_mem_nil, or_false] at hcr
      rcases hcr with rfl | rfl | rfl | rfl
      · exact hmem _ ⟨72, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by decide⟩
      · exact hmem _ ⟨73, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by decide⟩
      · exact hcount
      · exact hacc
  · intro j hj hj1 hj2
    have hlen : finalSampledIOTransitionGates.length = 4 := by decide
    have hpre : ((packedTableOptimized ++ alwaysOnOptimized) ++ crossRowSingletons ++
        queueWitnessGates).length = 78 := by decide
    apply hmem
    refine ⟨78 + j, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    simp only [List.get_eq_getElem, finalExtTransitionGates_split]
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega

/-- **The queue witness at VCL semantics, on every row**: core positions `76`/`77` are kept and
are the retargeted queue gates on `W0`/`W1`. -/
theorem queue_sources_vcl {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligations n env envF) :
    queueNonEmpty309.eval env = 0 ∧ queueTiling309.eval env = 0 := by
  have h1 := hsource.extensionCore packedQueueNonEmptyId (mem_keptCoreIds _ (by decide) (by decide))
  have h2 := hsource.extensionCore packedQueueTilingId (mem_keptCoreIds _ (by decide) (by decide))
  simp only [coreSemValue309, ↓reduceIte] at h1
  have hne : packedQueueTilingId ≠ packedQueueNonEmptyId := by decide
  simp only [coreSemValue309, hne, ↓reduceIte] at h2
  exact ⟨h1, h2⟩

end rows

/-! ## At the repaired chip -/

section chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **At `computeChipVCLD`, every nonterminal row has the decoded transition sources** (walk
recurrences on `W0`/`W1` included). -/
theorem computeChipVCLD_transition_sources {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hnotLast : (Reify.envOfTrace P orbit.ω x chalV pubVal).trace 12 = 0) :
    DecodedTransitionSourcesVCL (gather309 b (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))) := by
  have hall := ((computeChipVCLD_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP).2 x hx
  have hs := VclSourceObligations.of_vclGates n b _ (fun g hg => hall g (by
    simp only [vclGatesD, vclGatesA, List.mem_append]; exact Or.inl (Or.inl hg)))
  refine conditional_transition_soundness_vcl hs ?_
  change (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)).trace 12 = 0
  rw [pullEnv_trace_lt _ 12 (by norm_num)]
  exact hnotLast

/-- **At `computeChipVCLD`, the queue witness gates vanish on every row.** -/
theorem computeChipVCLD_queue_sources {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit) P)
    (x : F) (hx : x ∈ rowNodeSet nodes) :
    let env := gather309 b (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))
    queueNonEmpty309.eval env = 0 ∧ queueTiling309.eval env = 0 := by
  have hall := ((computeChipVCLD_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP).2 x hx
  exact queue_sources_vcl (VclSourceObligations.of_vclGates n b _ (fun g hg => hall g (by
    simp only [vclGatesD, vclGatesA, List.mem_append]; exact Or.inl (Or.inl hg))))

/-- The walk columns of the pull-back are the VCL walk columns `208..213`. -/
theorem pullEnv_walk (envV : Env F) (j : Fin 2) (k : Fin 3) :
    (pullEnv envV).trace (walkLimb j k) = envV.trace (walkColVCL j k) := by
  simp only [pullEnv, vclCol_walkLimb]

end chip

end

end VclL.Compute
end Nock.NockVMROM.Thm54
