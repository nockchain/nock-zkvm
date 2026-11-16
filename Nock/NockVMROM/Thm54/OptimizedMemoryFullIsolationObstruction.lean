import Nock.Tactic.DeriveFintypeFix
import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting

/-!
# Full-system selector-isolation obstruction

The fixed-mask obstruction was removed by replacing IDs 5/6.  A distinct obstruction remains for
the requested simultaneous isolation of selector IDs 0..3: exact recovery of the four per-state
intermediate equations and the read/verify inverse equations forces any one-hot assignment with
three Boolean selectors back to a Boolean fourth selector.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryFullIsolationObstruction

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

/-- The four exact production intermediate-delta sources. -/
def decomposeDeltaSource : Expr :=
  (gateByM MemoryTable.MState.decompose
    (.Sub (tc 32) (tc 31))).subst memorySubst

def haltDeltaSource : Expr :=
  (gateByM MemoryTable.MState.halt
    (.Sub (tc 32) (tc 31))).subst memorySubst

def readDeltaSource : Expr :=
  (gateByM MemoryTable.MState.read_root
    (.Sub (.Sub (tc 32) (tc 31)) (tc 33))).subst memorySubst

def verifyDeltaSource : Expr :=
  (gateByM MemoryTable.MState.verify_child
    (.Add (.Sub (tc 32) (tc 31)) (tc 33))).subst memorySubst

/-- The two exact record-touching inverse sources used by the obstruction. -/
def readInverseSource : Expr :=
  (gateByM MemoryTable.MState.read_root
    (.Sub (.Mul poleExpr (tc 33)) (.Const 1))).subst memorySubst

def verifyInverseSource : Expr :=
  (gateByM MemoryTable.MState.verify_child
    (.Sub (.Mul poleExpr (tc 33)) (.Const 1))).subst memorySubst

/-! Both classes are actual
fold sources, and at the one-hot selector the merged gate *is* the active branch
(`OptimizedMemoryGateBasis.mergedGate_subst_eval`), so the obstruction below is unchanged: it is
an argument about what a single owner per delta can enforce. -/

/-- Merged quantity class `23` — the `intermediate` delta — at fold index `24`. -/
theorem intermediateDeltaClass_index :
    extensionFoldSources (K := ℚ).get ⟨24, by decide⟩ =
      (MemoryFactorizationScope.mergedGate (K := ℚ) 23).subst memorySubst := rfl

/-- Merged quantity class `24` — the record-touching `pole · g = 1` — at fold index `25`. -/
theorem recordInverseClass_index :
    extensionFoldSources (K := ℚ).get ⟨25, by decide⟩ =
      (MemoryFactorizationScope.mergedGate (K := ℚ) 24).subst memorySubst := rfl

theorem selector_isolation_classes_are_actual_fold_sources :
    (MemoryFactorizationScope.mergedGate (K := ℚ) 23).subst memorySubst ∈
        extensionFoldSources (K := ℚ) ∧
      (MemoryFactorizationScope.mergedGate (K := ℚ) 24).subst memorySubst ∈
        extensionFoldSources (K := ℚ) := by
  refine ⟨?_, ?_⟩
  · rw [← intermediateDeltaClass_index]; exact List.get_mem _ _
  · rw [← recordInverseClass_index]; exact List.get_mem _ _

/-- The six equations are exactly the selector branches of those two classes. -/
theorem selector_isolation_sources_are_merged_branches :
    decomposeDeltaSource =
        (gateByM MemoryTable.MState.decompose
          (MemoryFactorizationScope.memQuantity (K := ℚ) MemoryTable.MState.decompose 23)).subst
          memorySubst ∧
      haltDeltaSource =
        (gateByM MemoryTable.MState.halt
          (MemoryFactorizationScope.memQuantity (K := ℚ) MemoryTable.MState.halt 23)).subst
          memorySubst ∧
      readDeltaSource =
        (gateByM MemoryTable.MState.read_root
          (MemoryFactorizationScope.memQuantity (K := ℚ) MemoryTable.MState.read_root 23)).subst
          memorySubst ∧
      verifyDeltaSource =
        (gateByM MemoryTable.MState.verify_child
          (MemoryFactorizationScope.memQuantity (K := ℚ) MemoryTable.MState.verify_child 23)).subst
          memorySubst ∧
      readInverseSource =
        (gateByM MemoryTable.MState.read_root
          (MemoryFactorizationScope.memQuantity (K := ℚ) MemoryTable.MState.read_root 24)).subst
          memorySubst ∧
      verifyInverseSource =
        (gateByM MemoryTable.MState.verify_child
          (MemoryFactorizationScope.memQuantity (K := ℚ) MemoryTable.MState.verify_child 24)).subst
          memorySubst :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact scalar shadow of the four gated memory-intermediate equations together with the two
record-touching inverse equations. -/
def SelectorDeltaLayer (s : Fin 4 → F73) (d g pole : F73) : Prop :=
  s 0 + s 1 + s 2 + s 3 = 1 ∧
  s 0 * d = 0 ∧
  s 1 * d = 0 ∧
  s 2 * (d - g) = 0 ∧
  s 3 * (d + g) = 0 ∧
  s 2 * (pole * g - 1) = 0 ∧
  s 3 * (pole * g - 1) = 0

inductive DeltaKind
  | decompose | halt | read | verify
  deriving DecidableEq, Fintype

def deltaCoefficient : DeltaKind → Int
  | .decompose | .halt => 0
  | .read => 1
  | .verify => -1

def activeTriple (target omitted : Fin 4) : Finset (Fin 4) :=
  Finset.univ.erase omitted

def selectorGateId (target : Fin 4) : Fin 14 := ⟨target, by omega⟩

def deltaKindOfFin (q : Fin 4) : DeltaKind :=
  match (q : ℕ) with
  | 0 => .decompose | 1 => .halt | 2 => .read | _ => .verify

/-- If a semantic delta source is assigned to exactly one production owner, it may be omitted only
when that owner is the isolated target gate. -/
def deltaCompatible (owner : DeltaKind → Fin 14) (target omitted : Fin 4) : Prop :=
  let enforced := (activeTriple target omitted).filter fun q =>
    owner (deltaKindOfFin q) ≠ selectorGateId target
  ∀ a ∈ enforced, ∀ b ∈ enforced,
    deltaCoefficient (deltaKindOfFin a) = deltaCoefficient (deltaKindOfFin b)

def DeltaIsolationNecessary (owner : DeltaKind → Fin 14) (target : Fin 4) : Prop :=
  match (target : ℕ) with
  | 0 | 1 =>
      (owner .decompose = selectorGateId target ∧ owner .halt = selectorGateId target) ∨
      owner .read = selectorGateId target ∨ owner .verify = selectorGateId target
  | 2 =>
      (owner .decompose = selectorGateId target ∧ owner .halt = selectorGateId target) ∨
      owner .read = selectorGateId target ∨
      (owner .decompose = selectorGateId target ∧ owner .verify = selectorGateId target) ∨
      (owner .halt = selectorGateId target ∧ owner .verify = selectorGateId target)
  | _ =>
      (owner .decompose = selectorGateId target ∧ owner .halt = selectorGateId target) ∨
      owner .verify = selectorGateId target ∨
      (owner .decompose = selectorGateId target ∧ owner .read = selectorGateId target) ∨
      (owner .halt = selectorGateId target ∧ owner .read = selectorGateId target)

theorem deltaCompatible_pair
    (owner : DeltaKind → Fin 14) (target omitted a b : Fin 4)
    (h : deltaCompatible owner target omitted)
    (ha : a ≠ omitted) (hb : b ≠ omitted)
    (hoa : owner (deltaKindOfFin a) ≠ selectorGateId target)
    (hob : owner (deltaKindOfFin b) ≠ selectorGateId target) :
    deltaCoefficient (deltaKindOfFin a) = deltaCoefficient (deltaKindOfFin b) := by
  apply h
  · simp [activeTriple, ha, hoa]
  · simp [activeTriple, hb, hob]

set_option maxHeartbeats 2000000 in
theorem delta_compatible_requires_target_ownership
    (owner : DeltaKind → Fin 14) (target omitted : Fin 4)
    (homit : omitted ≠ target) (h : deltaCompatible owner target omitted) :
    DeltaIsolationNecessary owner target := by
  classical
  by_cases hD : owner .decompose = selectorGateId target
  <;> by_cases hH : owner .halt = selectorGateId target
  <;> by_cases hR : owner .read = selectorGateId target
  <;> by_cases hV : owner .verify = selectorGateId target
  <;> fin_cases target <;> fin_cases omitted
  all_goals try { simp at homit }
  all_goals
    simp [DeltaIsolationNecessary, selectorGateId, hD, hH, hR, hV]
    <;> exfalso
    <;> first
      | have hc := deltaCompatible_pair owner _ _ 2 3 h (by decide) (by decide)
            (by simpa [deltaKindOfFin, selectorGateId] using hR)
            (by simpa [deltaKindOfFin, selectorGateId] using hV)
        norm_num [deltaKindOfFin, deltaCoefficient] at hc
      | have hc := deltaCompatible_pair owner _ _ 0 3 h (by decide) (by decide)
            (by simpa [deltaKindOfFin, selectorGateId] using hD)
            (by simpa [deltaKindOfFin, selectorGateId] using hV)
        norm_num [deltaKindOfFin, deltaCoefficient] at hc
      | have hc := deltaCompatible_pair owner _ _ 1 3 h (by decide) (by decide)
            (by simpa [deltaKindOfFin, selectorGateId] using hH)
            (by simpa [deltaKindOfFin, selectorGateId] using hV)
        norm_num [deltaKindOfFin, deltaCoefficient] at hc
      | have hc := deltaCompatible_pair owner _ _ 0 2 h (by decide) (by decide)
            (by simpa [deltaKindOfFin, selectorGateId] using hD)
            (by simpa [deltaKindOfFin, selectorGateId] using hR)
        norm_num [deltaKindOfFin, deltaCoefficient] at hc
      | have hc := deltaCompatible_pair owner _ _ 1 2 h (by decide) (by decide)
            (by simpa [deltaKindOfFin, selectorGateId] using hH)
            (by simpa [deltaKindOfFin, selectorGateId] using hR)
        norm_num [deltaKindOfFin, deltaCoefficient] at hc

/-- Finite exact ownership obstruction: no disjoint assignment of the four semantic delta sources
to production gates lets every selector target choose a three-active-state isolation pattern whose
remaining enforced deltas are compatible. -/
theorem no_disjoint_delta_ownership_supports_all_selector_isolations :
    ¬ ∃ owner : DeltaKind → Fin 14,
      ∀ target : Fin 4, DeltaIsolationNecessary owner target := by
  rintro ⟨owner, hall⟩
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  have h3 := hall 3
  simp [DeltaIsolationNecessary, selectorGateId] at h0 h1 h2 h3
  aesop

theorem all_four_selector_full_system_isolation_impossible :
    ¬ ∃ owner : DeltaKind → Fin 14,
      ∀ target : Fin 4, ∃ omitted : Fin 4,
        omitted ≠ target ∧ deltaCompatible owner target omitted := by
  rintro ⟨owner, hall⟩
  apply no_disjoint_delta_ownership_supports_all_selector_isolations
  refine ⟨owner, fun target => ?_⟩
  obtain ⟨omitted, homit, hcompat⟩ := hall target
  exact delta_compatible_requires_target_ownership owner target omitted homit hcompat

end OptimizedMemoryFullIsolationObstruction
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryFullIsolationObstruction.delta_compatible_requires_target_ownership
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryFullIsolationObstruction.all_four_selector_full_system_isolation_impossible
