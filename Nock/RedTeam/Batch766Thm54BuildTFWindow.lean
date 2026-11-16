/-
  Nock/RedTeam/Batch766Thm54BuildTFWindow.lean

  * **(A) Import walk.**
  * **(C) C3 controls.**  Tightness (a path forest attains `size = h` at its root, so `≤ h` cannot
    be lowered) and necessity of `kroots ≤ h` for the root sum.
  * **(D) N3 controls.**  A concrete one-row skeleton fixes the `1`-indexing of `requestTargets`
    (slot `k` at exponent `k + 1`; `0` and past-the-end read `atom 0`; `decompose` reads `atom 0`).
-/
import Lean
import Nock.NockVMROM.Thm54.BuildTFWindow
import Nock.NockVMROM.Thm54.TraceGen.GenRequestTargets
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch766

open Lean Elab Command Nock Nock.Walk

/-! ## (A) Import walk -/

def importsOf (env : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for i in [0:env.header.moduleNames.size] do
    m := m.insert env.header.moduleNames[i]! (env.header.moduleData[i]!.imports.map (·.module))
  return m

partial def importClosure (g : Std.HashMap Name (Array Name)) (root : Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := [root]
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      for c in g.getD n #[] do
        unless seen.contains c do work := c :: work
  return seen

def pinnedMod : Name := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
def carrierMod : Name := `Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

run_cmd do
  let env ← getEnv
  let g := importsOf env
  let btf := `Nock.NockVMROM.Thm54.BuildTFWindow
  let grt := `Nock.NockVMROM.Thm54.TraceGen.GenRequestTargets
  let cl := importClosure g btf
  if cl.contains pinnedMod || cl.contains carrierMod then
    throwError m!"STOP: {btf} reaches the pinned file or the carrier"
  for n in cl.toList do
    if (g.getD n #[]).contains pinnedMod then throwError m!"STOP: {n} imports the pinned file"
  let pcl := importClosure g pinnedMod
  if pcl.contains grt then
    throwError "STOP: the pinned file's closure contains GenRequestTargets"
  logInfo m!"pinned closure contains BuildTFWindow: {pcl.contains btf} (expected since the 36th move)"
  unless (importClosure g grt).contains pinnedMod do
    throwError "expected GenRequestTargets above the pinned file (disclosure changed)"
  -- positive control
  unless (g.getD `Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists #[]).contains pinnedMod do
    throwError "positive control failed: OptimizedCanonicalHostileLists should import the pinned file"
  logInfo m!"BuildTFWindow: {cl.size} modules in its closure, pinned file and carrier absent \
    (below the pinned file). GenRequestTargets reaches the pinned file (it sits above it); the pinned \
    file's {pcl.size}-module closure does not contain GenRequestTargets. Positive control: ok"


def delivered : List Name := [
  `Nock.Walk.buildTF_size_eq, `Nock.Walk.buildTF_block_size_le,
  `Nock.Walk.buildTF_size_le_of_bfsValidF, `Nock.Walk.buildTF_size_le_h_of_bfsValidF,
  `Nock.Walk.buildTF_roots_size_sum_le,
  `Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leaves_le_size,
  `Nock.NockVMROM.Thm54.PreSeedCensus.preZNounOfEnvs_leaves_le,
  `Nock.NockVMROM.Thm54.PreSeedCensus.reqPairsOfEnvs_fst_leaves_le,
  `Nock.NockVMROM.Thm54.PreSeedCensus.preZNounOfEnvs_roots_leaves_sum_le,
  `Nock.NockVMROM.Thm54.TraceGen.requestList_getElem_slot,
  `Nock.NockVMROM.Thm54.TraceGen.prefix_records_length,
  `Nock.NockVMROM.Thm54.TraceGen.requestTargets_congr,
  `Nock.NockVMROM.Thm54.TraceGen.goodReq_extractNodeReqs,
  `Nock.NockVMROM.Thm54.TraceGen.genMemForestFromTree_requestTargets,
  `Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_requestTargets,
  `Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_requestTargets_row]

run_cmd do
  let std : List Name := [`propext, `Classical.choice, `Quot.sound]
  for n in delivered do
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      unless std.contains a do throwError m!"{n} depends on {a}"
  let axs ← liftCoreM (Lean.collectAxioms ``Classical.choice)
  unless axs.contains `Classical.choice do throwError "positive control failed"
  logInfo m!"{delivered.length} delivered names: only propext / Classical.choice / Quot.sound"

/-! ## (C) C3 controls -/

/-- A path forest: one root, rows `1, 2` have one child each, row `3` is a leaf. -/
def foPath : ℕ → ℕ := fun i => if i < 3 then 1 else 0

private theorem c1 : childIdxsF 1 foPath 3 1 = [2] := by
  simp [childIdxsF, firstCF, Sf, foPath]
private theorem c2 : childIdxsF 1 foPath 3 2 = [3] := by
  simp [childIdxsF, firstCF, Sf, foPath, Finset.filter_singleton]
private theorem c3 : childIdxsF 1 foPath 3 3 = [] := by
  simp [childIdxsF, firstCF, Sf, foPath]

private theorem s3 : (buildTF 1 foPath (fun _ => ()) 3 3).size = 1 := by
  rw [buildTF_size_eq, c3]; rfl
private theorem s2 : (buildTF 1 foPath (fun _ => ()) 3 2).size = 2 := by
  rw [buildTF_size_eq, c2]; simp [s3]

/-- **Tightness.**  The root subtree of the path forest has exactly `h = 3` nodes, so the
window `size ≤ h` (`buildTF_size_le_h_of_bfsValidF`) cannot be lowered. -/
theorem path_root_size_eq : (buildTF 1 foPath (fun _ => ()) 3 1).size = 3 := by
  rw [buildTF_size_eq, c1]; simp [s2]

/-- The path forest is queue-valid. -/
theorem path_bfsValid : BFSValidF 1 foPath 3 := by
  intro i hi hih
  interval_cases i <;> decide

/-- **Consistency with the lemma.**  The lemma at `i = 1` gives `≤ 3`; the control attains it. -/
example : (buildTF 1 foPath (fun _ => ()) 3 1).size ≤ 3 :=
  buildTF_size_le_h_of_bfsValidF _ path_bfsValid (by omega) (by omega)

/-- **Necessity of `kroots ≤ h`.**  With `kroots = 2 > h = 1` the two root subtrees together
have `2 > h` nodes. -/
theorem roots_exceed_without_hk :
    ∑ i ∈ Finset.Icc 1 2, (buildTF 2 (fun _ => 0) (fun _ => ()) 1 i).size = 2 := by
  have : ∀ i, (buildTF 2 (fun _ => 0) (fun _ => ()) 1 i).size = 1 := by
    intro i
    rw [buildTF_size_eq]
    simp [childIdxsF]
  simp [this]

/-! ## (D) N3 controls: `requestTargets` is `1`-indexed, compute-BFS x slot -/

section N3

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.PreSeedCensus Nock.NockVMROM.Thm54.TraceGen

/-- One compute row in state `s0` (two records): record `i` has root `atom (i+1)` and child
`atom (i+11)`. -/
def row0 : ComputeRowSkeleton where
  state := .s0
  subject := .atom 0
  formula := .atom 0
  evaluation := .atom 0
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun i _ => ⟨.atom ((i : ℕ) + 1), .atom ((i : ℕ) + 11), 0⟩

def S0 : SemanticSkeleton := ⟨.node row0 [], []⟩

theorem rows0 : computeSkeletonRows S0 = [row0] := by
  unfold computeSkeletonRows S0
  rw [bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem requestList_S0 :
    requestList S0 = [⟨.atom 1, .atom 11, 0⟩, ⟨.atom 2, .atom 12, 0⟩] := by
  rw [requestList_eq, rows0]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hl : (rowRecords row0).length = 2 := by rw [rowRecords_length]; rfl
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 2
  · have hk' : k < Nock.Framework.recordCount row0.state := by
      show k < 2; exact hk
    rw [rowRecords_getElem row0 k hk']
    interval_cases k <;> rfl
  · have : (rowRecords row0)[k]? = none := List.getElem?_eq_none (by omega)
    rw [this]
    simp; omega

example : requestTargets S0 .read_root 1 = .atom 1 := by simp [requestTargets, requestList_S0]
example : requestTargets S0 .read_root 2 = .atom 2 := by simp [requestTargets, requestList_S0]
example : requestTargets S0 .verify_child 1 = .atom 11 := by simp [requestTargets, requestList_S0]
example : requestTargets S0 .verify_child 2 = .atom 12 := by simp [requestTargets, requestList_S0]
example : requestTargets S0 .read_root 0 = .atom 0 := by simp [requestTargets]
example : requestTargets S0 .read_root 3 = .atom 0 := by simp [requestTargets, requestList_S0]
example : requestTargets S0 .decompose 1 = .atom 0 := by simp [requestTargets]
/-- Negative control: a `0`-indexed reading would put record `1` (root `atom 2`) at exponent `1`;
the real table puts record `0` there. -/
example : requestTargets S0 .read_root 1 ≠ .atom 2 := by
  simp [requestTargets, requestList_S0]

end N3

end Nock.RedTeam.Batch766
