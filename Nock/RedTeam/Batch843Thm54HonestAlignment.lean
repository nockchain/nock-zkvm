/-
  Nock/RedTeam/Batch843Thm54HonestAlignment.lean

  * **`typed_state_honest`** (every package, no premise): at the package's canonical compute trace,
    the typed decoded state of row `i` is `exec.computePubAt i`'s state (the selector columns are
    `encodeBase` of it, `honestRow_base`, `decodeState_encodedRowAt`);
  * **`lblCAt_state_honest`** (every package, every tuple `c`): the same for the family label
    (`Batch842.lblCAt_state_eq_typed`);
  * under the honest execution's compute topology `htopE : ComputeExactTopology exec`
    (`Fcomp`'s first conjunct `pub.state = label.1`; fanout = children):
    **`typed_state_eq_exec`** (`= (exec.computeRowAt i).1`, the exec LABEL state),
    **`typedComputeRows_fst_eq_exec`**, **`tiles_queued_honest`**, and
    **`expOf_requestList_honest`**: `Batch773.expOf_requestList` instantiated at the canonical trace
    with `hsat := canonicalComputeTrace_satisfies` — the package-level instance;
  * **`expOf_requestList_built`**: at every BUILT package (`buildFullPackage E …`, the term
    `exists_package_of_carrier` introduces under `nockCompiles_p66…p76`, so the generated package
    `E := genBuildableOfProgram …` in particular), `htopE` is `E.traversal.1`
    (`BuildablePackage.constructed_same_execution`: `family.problem.exec = E.exec`, `rfl`).

  Reach : `typed_state_*`, `lblCAt_state_*`, `typedComputeRows_fst_eq_exec`,
  `tiles_queued_honest` reach none of the probes.  `expOf_requestList_honest` reaches `Vmem` /
  `interV` through `canonicalComputeTrace_satisfies` (honest canonical satisfaction), and
  `tiles_queued_built` reaches `Vmem` through the carrier's `MemoryExactTopology` (`Fmem`, the
  type of `E.traversal`).

  Scope: the full `State × DTcomp` label is NOT identified — the family decoder reads the tuple's
  coins (fingerprints at `c`), and `Batch374` records that the honest identification of the data
  component is not `rfl`.  No consumer of the alignment reads it.  Rule 8: every theorem here holds
  at every `(c)` and needs no event (honest side).
-/
import Nock.RedTeam.Batch842Thm54WalkGateBridge
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.RedTeam.Batch774Thm54HonestAlignment
import Nock.NockVMROM.Thm54.OptimizedHostileConfiguration
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch843

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- At the canonical trace the selector base columns are the exec row's one-hot state. -/
theorem honest_base_selector (i : Fin P.optimized.family.problem.cfg.compRows) (s : State) :
    (rowEnv P (honestComputeTrace P) i).baseTrace ⟨opCol s, by cases s <;> decide⟩ =
      if s = (P.optimized.family.problem.exec.computePubAt i).state then 1 else 0 := by
  have h := honestRow_base P i ⟨opCol s, by cases s <;> decide⟩
  change (rowEnv P (honestComputeTrace P) i).baseTrace _ =
    OptimizedComputeFinalTrace.finalBaseCell P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos i _ at h
  rw [h]
  have hlt : opCol s < 11 := by cases s <;> decide
  simp only [OptimizedComputeFinalTrace.finalBaseCell, dif_pos hlt,
    OptimizedComputeSampledTrace.encodedRowAt, OptimizedComputeOverlay.sampledEncode,
    OptimizedComputeCodec.encodeBase]
  generalize (P.optimized.family.problem.exec.computePubAt i).state = st
  cases s <;> cases st <;> simp [opCol, OptimizedComputeCodec.stateIndex]

/-- **The typed decoded state at the canonical trace is the exec row's state** (every package). -/
theorem typed_state_honest (i : Fin P.optimized.family.problem.cfg.compRows) :
    (typedComputeLabel P (honestComputeTrace P) i).1 =
      (P.optimized.family.problem.exec.computePubAt i).state := by
  simp only [typedComputeLabel]
  apply computeStateOf_of_oneHot
  intro s
  have hs : opCol s < 11 := by cases s <;> decide
  rw [Batch842.decodeSource_trace_lt11 _ _ hs]
  have hb := honest_base_selector P i s
  rw [show (⟨opCol s, by omega⟩ : Fin 13) = ⟨opCol s, by cases s <;> decide⟩ from rfl, hb]
  split_ifs <;> simp

/-- **The family decoded state at the canonical trace, at every tuple `c`.** -/
theorem lblCAt_state_honest (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (lblCAt P (honestComputeTrace P) c i).1 =
      (P.optimized.family.problem.exec.computePubAt i).state :=
  (Batch842.lblCAt_state_eq_typed P _ c i).trans (typed_state_honest P i)

section Topology

variable (htopE : ComputeExactTopology P.optimized.family.problem.exec)
include htopE

omit [Fintype F] [DecidableEq F] in
/-- Every BFS node of the exec compute tree satisfies `Fcomp`. -/
theorem exec_node_fcomp :
    ∀ t ∈ bfsForest [P.optimized.family.problem.exec.computeTree],
      t.label.2.2.1.state = t.label.1 ∧
        fanoutComp t.label.1 = t.children.length := by
  intro t ht
  have hin : InTree P.optimized.family.problem.exec.computeTree t := by
    rw [mem_bfsForest] at ht
    obtain ⟨root, hroot, hin⟩ := ht
    simp only [List.mem_singleton] at hroot
    subst root
    exact hin
  have hF := ((RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) _).1 htopE.1 t hin).1
  have hf := fanout_eq_children_length_of_properArity (ComputeTable.comp_stateSep (K := K))
    htopE.1 htopE.2 t hin
  exact ⟨hF.1, hf⟩

omit [Fintype F] [DecidableEq F] in
/-- The exec row's pub state is its label state. -/
theorem exec_row_state (i : Fin P.optimized.family.problem.cfg.compRows) :
    (P.optimized.family.problem.exec.computePubAt i).state =
      (P.optimized.family.problem.exec.computeRowAt i).1 := by
  have hmem : P.optimized.family.problem.exec.computeRowAt i ∈
      P.optimized.family.problem.exec.computeRows := List.get_mem _ _
  simp only [ExactExecution.computeRows, List.mem_map] at hmem
  obtain ⟨t, ht, hlab⟩ := hmem
  have := (exec_node_fcomp P htopE t ht).1
  show (P.optimized.family.problem.exec.computeRowAt i).2.2.1.state =
    (P.optimized.family.problem.exec.computeRowAt i).1
  rw [← hlab]
  exact this

/-- **`lblC = exec label` (state).**  The typed decoded state at the canonical trace is the exec
compute row's LABEL state. -/
theorem typed_state_eq_exec (i : Fin P.optimized.family.problem.cfg.compRows) :
    (typedComputeLabel P (honestComputeTrace P) i).1 =
      (P.optimized.family.problem.exec.computeRowAt i).1 :=
  (typed_state_honest P i).trans (exec_row_state P htopE i)

theorem lblCAt_state_eq_exec (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (lblCAt P (honestComputeTrace P) c i).1 =
      (P.optimized.family.problem.exec.computeRowAt i).1 :=
  (Batch842.lblCAt_state_eq_typed P _ c i).trans (typed_state_eq_exec P htopE i)

/-- The typed rows' states are the exec rows' states. -/
theorem typedComputeRows_fst_eq_exec :
    (typedComputeRows P (honestComputeTrace P)).map Prod.fst =
      P.optimized.family.problem.exec.computeRows.map Prod.fst := by
  apply List.ext_getElem
  · simp [typedComputeRows_length, ExactExecution.computeRows_length]
  · intro n h1 h2
    have hn : n < P.optimized.family.problem.cfg.compRows := by
      simpa [typedComputeRows_length] using h1
    simp only [List.getElem_map, typedComputeRows, List.getElem_finRange]
    rw [typed_state_eq_exec P htopE]
    simp [ExactExecution.computeRowAt]

theorem map_fanout_eq_exec :
    (typedComputeRows P (honestComputeTrace P)).map computeFanout =
      P.optimized.family.problem.exec.computeRows.map computeFanout := by
  have h := congrArg (List.map fanoutComp) (typedComputeRows_fst_eq_exec P htopE)
  simp only [List.map_map] at h
  have e : ∀ l : List (State × DTcomp K), l.map computeFanout = l.map (fanoutComp ∘ Prod.fst) :=
    fun l => List.map_congr_left (fun x _ => by rcases x with ⟨_, _⟩; rfl)
  rw [e, e]
  exact h

/-- **Both walk-gate premises of `expOf_requestList` at the canonical trace.** -/
theorem tiles_queued_honest :
    Batch771.Tiles computeFanout 1 (typedComputeRows P (honestComputeTrace P)) ∧
      Batch771.Queued computeFanout 1 (typedComputeRows P (honestComputeTrace P)) := by
  have hwf : Batch771.FanoutWF computeFanout [P.optimized.family.problem.exec.computeTree] :=
    fun t ht => ((exec_node_fcomp P htopE t ht).2).symm
  have ht := Batch774.tiles_of_bfs computeFanout [P.optimized.family.problem.exec.computeTree]
    (by simp) hwf
  have hq := Batch774.queued_of_bfs computeFanout [P.optimized.family.problem.exec.computeTree]
    (by simp) hwf
  have hm := map_fanout_eq_exec P htopE
  have hlen : (typedComputeRows P (honestComputeTrace P)).length =
      P.optimized.family.problem.exec.computeRows.length := by
    simpa using congrArg List.length hm
  change Batch771.Tiles computeFanout 1 P.optimized.family.problem.exec.computeRows at ht
  change Batch771.Queued computeFanout 1 P.optimized.family.problem.exec.computeRows at hq
  refine ⟨?_, ?_⟩
  · unfold Batch771.Tiles at ht ⊢
    rw [hm, hlen]; exact ht
  · intro i hi
    rw [hlen] at hi
    have := hq i hi
    rw [List.map_take, hm, ← List.map_take]
    exact this

/-- **The package-level honest instance of S5** (`Batch773.expOf_requestList` at an actual trace
with `hsat` and the typed rows equal, state-wise, to the exec's labels). -/
theorem expOf_requestList_honest
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (S : SemanticStrategy.SemanticSkeleton) (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) (subj formula : Noun)
    (hS : S.computeTree = mapComputeJoinIn q forest
      (typedComputeTree P (honestComputeTrace P)) subj formula)
    (a : Fin (rows P)) (j : Fin 3) (hact : activeMask (rowEnv P (honestComputeTrace P) a) j = 1) :
    ∃ (ha : (a : ℕ) < (SemanticStrategy.computeSkeletonRows S).length)
      (hj : (j : ℕ) < Nock.Framework.recordCount (SemanticStrategy.computeSkeletonRows S)[(a : ℕ)].state),
      (PreSeedCensus.requestList S)[expOf P (honestComputeTrace P) a j - 1]? =
        some ((SemanticStrategy.computeSkeletonRows S)[(a : ℕ)].memoryRecord
          ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj) := by
  have hsat : RAP.SatisfiesWithPreprocessing P.computeChip (honestComputeTrace P) :=
    MultiRootOptimizedAcceptance.canonicalComputeTrace_satisfies P hax hbasis hwidth
  obtain ⟨ht, hq⟩ := tiles_queued_honest P htopE
  exact Batch773.expOf_requestList P (honestComputeTrace P) hsat
    (OptimizedHostileConfiguration.hchar_of_package P) ht hq S q forest subj formula hS a j hact

end Topology

end

/-! ## At every built package (hence the generated one): `htopE` is the carrier's -/

section Built

open BuildablePackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **The honest alignment instance at every built package** (`buildFullPackage E I R …`, the
package `exists_package_of_carrier` introduces): the exec compute topology is `E.traversal.1`
(`family.problem.exec = E.exec` by `rfl`, `constructed_same_execution`). -/
theorem tiles_queued_built (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    let P := buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF
    Batch771.Tiles computeFanout 1 (typedComputeRows P (honestComputeTrace P)) ∧
      Batch771.Queued computeFanout 1 (typedComputeRows P (honestComputeTrace P)) :=
  tiles_queued_honest _ E.traversal.1

end Built

end Nock.RedTeam.Batch843

#print axioms Nock.RedTeam.Batch843.typed_state_honest
#print axioms Nock.RedTeam.Batch843.lblCAt_state_honest
#print axioms Nock.RedTeam.Batch843.typed_state_eq_exec
#print axioms Nock.RedTeam.Batch843.tiles_queued_honest
#print axioms Nock.RedTeam.Batch843.expOf_requestList_honest
#print axioms Nock.RedTeam.Batch843.tiles_queued_built
