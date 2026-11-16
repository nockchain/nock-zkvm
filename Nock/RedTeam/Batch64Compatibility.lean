import Nock.NockVMROM.Thm54.OptimizedMemoryConcrete
import Nock.RedTeam.Batch63Compatibility

/-!

The fold is therefore a
pre-partition fold — no disjoint bucket assignment, every source folded — of whatever the
current census is, over the same twenty-one `i % 21` buckets.

The alias is still needed by `Batch64.sampledTerminalCoord_redundant_under_fold_collision`
(`Batch64Thm54RepairedOptimizedMemory.lean:189`) and its accumulator twin: those reach the
sampled terminal source, which is `promotedTerminal` in `sourceAuthority`
and so is **absent** from the production `extensionFoldSources`. Only the pre-partition fold
covers it. -/

namespace Nock.RedTeam.Batch64

open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.Concrete
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryCodec
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.Concrete
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace.Concrete
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable section

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

def intermediateChainCoord {F : Type} [Field F] : CoeffExpr F :=
  CoeffExpr.mul (CoeffExpr.sub (CoeffExpr.const 1) (bcur (F := F) 5))
    (CoeffExpr.sub (extCoord (F := F) .traceCur 28 0)
      (extCoord (F := F) .traceNext 27 0))

def repairedSemanticBaseGates {F : Type} [Field F] : List (CoeffExpr F) :=
  (List.ofFn (sampledTerminalCoord (F := F))) ++
    (List.ofFn (sampledAccumulatorCoord (F := F))) ++
    [intermediateChainCoord]

def baseTransitionGates {F : Type} [Field F] : List (CoeffExpr F) :=
  [bbool (F := F) (bcur (F := F) 0), bbool (F := F) (bcur (F := F) 1),
   bbool (F := F) (bcur (F := F) 2), bbool (F := F) (bcur (F := F) 3),
   bsum4 (F := F) .traceCur,
   bbool (F := F) (bcur (F := F) 4), bbool (F := F) (bcur (F := F) 5)] ++
    repairedSemanticBaseGates

theorem repairedSemanticBaseGates_nodup {F : Type} [Field F] :
    (repairedSemanticBaseGates (F := F)).Nodup := by
  simp [repairedSemanticBaseGates, sampledTerminalCoord, sampledAccumulatorCoord,
    intermediateChainCoord, extCoord, bcur]

theorem repairedSemanticBaseGates_no_literal_zero {F : Type} [Field F] :
    ∀ g ∈ repairedSemanticBaseGates (F := F), g ≠ .const 0 := by
  intro g hg
  simp only [repairedSemanticBaseGates, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
    fin_cases k <;> simp [sampledTerminalCoord, extCoord]
  · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
    fin_cases k <;> simp [sampledAccumulatorCoord, extCoord]
  · simp only [List.mem_singleton] at hg
    subst g
    simp [intermediateChainCoord, extCoord, bcur]

def repairedBaseMutation {F : Type} [Field F] (j : Fin 7) : Env F where
  trace i :=
    if i = 0 then 1
    else if i =
      (if (j : ℕ) < 3 then 126 + (j : ℕ)
       else if (j : ℕ) < 6 then 138 + ((j : ℕ) - 3)
       else 90) then 1
    else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- Proof-only addition. -/
theorem repairedSemanticBaseGates_get {F : Type} [Field F] (j : Fin 7) :
    (repairedSemanticBaseGates (F := F)).get j =
      (repairedSemanticBaseGates (F := F))[(j : ℕ)]'(by
        have := j.isLt
        simp [repairedSemanticBaseGates]) := rfl

theorem repaired_base_gate_discrimination {F : Type} [Field F] (j : Fin 7) :
    let env := repairedBaseMutation (F := F) j
    let target := (repairedSemanticBaseGates (F := F)).get j
    target.eval env = 1 ∧
      (∀ g ∈ baseTransitionGates (F := F), g ≠ target → g.eval env = 0) := by
  fin_cases j <;>
    (try simp only [repairedSemanticBaseGates_get]) <;>
    simp [repairedBaseMutation, repairedSemanticBaseGates, sampledTerminalCoord,
      sampledAccumulatorCoord, intermediateChainCoord, extCoord, baseTransitionGates,
      bbool, bcur, bsum4, CoeffExpr.eval]

abbrev foldChallenge : Expr := Nock.RedTeam.Batch63.foldChallenge
noncomputable abbrev sourceIndices {K : Type} [Field K] :
    List (Fin (transitionSources (K := K)).length) :=
  Nock.RedTeam.Batch63.sourceIndices (K := K)
noncomputable abbrev foldAt {K : Type} [Field K] (j : Fin 21) : Expr :=
  Nock.RedTeam.Batch63.foldAt (K := K) j
noncomputable abbrev extensionTransitionGates {K : Type} [Field K] : List Expr :=
  Nock.RedTeam.Batch63.extensionTransitionGates (K := K)
abbrev FoldCollisionExcluded {K : Type} [Field K] (env : Env K) : Prop :=
  Nock.RedTeam.Batch63.FoldCollisionExcluded (K := K) env

theorem source_to_fold_complete {K : Type} [Field K] (env : Env K)
    (h : ∀ e ∈ transitionSources (K := K), e.eval env = 0) :
    ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0 :=
  Nock.RedTeam.Batch63.source_to_fold_complete (K := K) env h

theorem fold_to_source_of_collision_excluded {K : Type} [Field K] (env : Env K)
    (hfold : ∀ g ∈ extensionTransitionGates (K := K), g.eval env = 0)
    (hcollision : FoldCollisionExcluded env) :
    ∀ e ∈ transitionSources (K := K), e.eval env = 0 :=
  Nock.RedTeam.Batch63.fold_to_source_of_collision_excluded (K := K) env hfold hcollision

theorem honest_repaired_ids_7_13_named_rejection (j : Fin 7) :
    let target := (repairedSemanticBaseGates (F := F73)).get j
    let pivot :=
      if (j : ℕ) < 3 then 126 + (j : ℕ)
      else if (j : ℕ) < 6 then 138 + ((j : ℕ) - 3)
      else 90
    target.eval
      (mutateCurrentTrace
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex)
        pivot 1) = 1 := by
  have hzero := canonical_baseTransitionGates honestSampled honestProduction
    honestMemoryNodes honestMemoryNodes_injective basis73 honestMemoryChalVal
    honestMemoryPubVal strictOrbit honestMemoryPins honestMemoryNodes_aligned
    honestMemoryDenominatorsSafe honestReadMemoryIndex
  have htarget :
      ((repairedSemanticBaseGates (F := F73)).get j).eval
        (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73
          honestMemoryChalVal honestMemoryPubVal strictOrbit honestReadMemoryIndex) = 0 := by
    fin_cases j
    · apply hzero
      try simp only [repairedSemanticBaseGates_get]
      simp [Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.foldedBaseTransitionGates,
        semanticBaseTail, repairedSemanticBaseGates]
    · apply hzero
      try simp only [repairedSemanticBaseGates_get]
      simp [Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.foldedBaseTransitionGates,
        semanticBaseTail, repairedSemanticBaseGates]
    · apply hzero
      try simp only [repairedSemanticBaseGates_get]
      simp [Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.foldedBaseTransitionGates,
        semanticBaseTail, repairedSemanticBaseGates]
    · apply hzero
      try simp only [repairedSemanticBaseGates_get]
      simp [Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.foldedBaseTransitionGates,
        semanticBaseTail, repairedSemanticBaseGates]
    · apply hzero
      try simp only [repairedSemanticBaseGates_get]
      simp [Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.foldedBaseTransitionGates,
        semanticBaseTail, repairedSemanticBaseGates]
    · apply hzero
      try simp only [repairedSemanticBaseGates_get]
      simp [Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.foldedBaseTransitionGates,
        semanticBaseTail, repairedSemanticBaseGates]
    · try simp only [repairedSemanticBaseGates_get]
      simpa [repairedSemanticBaseGates, intermediateChainCoord, chainCoord] using
        canonical_chainCoord_zero honestSampled honestProduction honestMemoryNodes
          honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal
          strictOrbit honestMemoryNodes_aligned honestReadMemoryIndex (0 : Fin 3)
  fin_cases j
  all_goals
    try simp only [repairedSemanticBaseGates_get] at htarget ⊢
  all_goals
    simp [repairedSemanticBaseGates, sampledTerminalCoord, sampledAccumulatorCoord,
      intermediateChainCoord, extCoord, mutateCurrentTrace, CoeffExpr.eval, bcur] at htarget ⊢
  all_goals try linear_combination htarget
  have hb5 := canonical_base_current honestSampled honestMemoryNodes
    honestMemoryNodes_injective basis73 honestMemoryChalVal honestMemoryPubVal strictOrbit
    honestReadMemoryIndex (5 : Fin 6)
  have hb5zero :
      (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73 honestMemoryChalVal
        honestMemoryPubVal strictOrbit honestReadMemoryIndex).trace 5 = 0 := by
    rw [show (canonicalPhysicalEnv honestSampled honestMemoryNodes basis73 honestMemoryChalVal
      honestMemoryPubVal strictOrbit honestReadMemoryIndex).trace 5 =
        (encodedRowAt (F := F73) honestSampled honestReadMemoryIndex).base 5 by
          simpa using hb5]
    have hnot : (2 : ℕ) ≠ honestLegacyFamily.problem.cfg.memRows := by
      change 2 ≠
        (Nock.NockVMROM.Thm54.ConcreteStrictPackage.cfg honestSeed honestAlpha).memRows
      norm_num [Nock.NockVMROM.Thm54.ConcreteStrictPackage.cfg]
    simp [encodedRowAt, encode, encodeBase, semanticRowAt, lastMask, honestReadMemoryIndex,
      hnot]
  rw [hb5zero] at htarget ⊢
  rcases htarget with hbad | hdiff
  · exfalso
    exact (one_ne_zero : (1 : F73) ≠ 0) (by simpa using hbad)
  · linear_combination hdiff

end
end Nock.RedTeam.Batch64
