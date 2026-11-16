/-
  Nock/NockVMROM/Thm54/P8Core/SVWalk/ComputeTree.lean

  **The walk instance's compute `tree` / `shape` and `tree_shape`,
  package-free.**

  * `treeOfRows st lab S N` — the S-carrying exec tree (`StrategyOfTracesR0AC2.c2TreeOfTraces`'s
    shape: `reconTree` at the state fanouts of the 1-indexed row labels `((st i, lab i), S i)`);
    `shapeOfRows st S N` — its B0 skeleton `reconTree` of `(st i, S i)`;
  * `tree_shape` : `shapeOfTree (treeOfRows st lab S N) = shapeOfRows st S N` (any `st`, `lab`,
    `S`: the shape reads only the states and carriers, `mapNTree_reconTree`);
    `shapeOfRows_size_le` : `size ≤ N` at `1 ≤ N` (`ReconTreeSize.reconTree_size_le`);
  * the 309 row decode: `rowLabel env` (= `lblCAt`'s body: state `computeStateOf (decodeSource env)`,
    inputs, publics, decomposition), `rowState`, `rowCarrier` (`natLift` of column `302`), and the
    B0 readers `stateOfBase` / `stateB0` over the base columns `1 … 10`, with
    `computeStateOf_decodeSource` : the decoded state of a row is `stateOfBase` of its base selectors
    (so the shape is a function of the round-0 columns; `stateB0_round0`).
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVWalk

open scoped Polynomial
open Nock Nock.Reified Nock.Walk
open Nock.ComputeTable (State DTcomp fanoutComp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.SVFrame (shapeOfTree table309 B0Cols b0)

noncomputable section

/-! ## 1. The generic tree and shape -/

section Generic

variable {Kf : Type}

/-- The S-carrying exec tree over 1-indexed row data. -/
def treeOfRows (st : ℕ → State) (lab : ℕ → DTcomp Kf) (S : ℕ → ℕ) (N : ℕ) :
    NTree ((State × DTcomp Kf) × ℕ) :=
  reconTree (fun i => fanoutComp (st i)) (fun i => ((st i, lab i), S i)) N

/-- Its B0 skeleton: states and carriers only. -/
def shapeOfRows (st : ℕ → State) (S : ℕ → ℕ) (N : ℕ) : NTree (State × ℕ) :=
  reconTree (fun i => fanoutComp (st i)) (fun i => (st i, S i)) N

/-- **`tree_shape`**: the shape of the tree is the skeleton of states and carriers. -/
theorem tree_shape (st : ℕ → State) (lab : ℕ → DTcomp Kf) (S : ℕ → ℕ) (N : ℕ) :
    shapeOfTree (treeOfRows st lab S N) = shapeOfRows st S N := by
  unfold shapeOfTree treeOfRows shapeOfRows
  exact ReconTreeSize.mapNTree_reconTree _ _ _ _

/-- **`shape_size`**: at most `N` nodes. -/
theorem shapeOfRows_size_le (st : ℕ → State) (S : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N) :
    (shapeOfRows st S N).size ≤ N :=
  ReconTreeSize.reconTree_size_le _ _ _ hN

theorem treeOfRows_size_le (st : ℕ → State) (lab : ℕ → DTcomp Kf) (S : ℕ → ℕ) (N : ℕ)
    (hN : 1 ≤ N) : (treeOfRows st lab S N).size ≤ N :=
  ReconTreeSize.reconTree_size_le _ _ _ hN

/-- The tree's shape determines its round-local reading: two trees whose row data agree on
`st`, `lab`, `S` are equal (the `tree_round` field reduces to agreement of the row data). -/
theorem treeOfRows_congr {st st' : ℕ → State} {lab lab' : ℕ → DTcomp Kf} {S S' : ℕ → ℕ} {N : ℕ}
    (h1 : st = st') (h2 : lab = lab') (h3 : S = S') :
    treeOfRows st lab S N = treeOfRows st' lab' S' N := by
  subst h1 h2 h3; rfl

end Generic

/-! ## 2. The 309 row decode -/

section Decode

variable {F K : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq K]

/-- `computeStateOf` read on base-field selector values. -/
def stateOfBase (sel : ℕ → F) : State :=
  if sel 1 = 1 then .s1
  else if sel 2 = 1 then .s2
  else if sel 3 = 1 then .s3
  else if sel 4 = 1 then .s4
  else if sel 5 = 1 then .s5
  else if sel 6 = 1 then .s6
  else if sel 7 = 1 then .s7
  else if sel 8 = 1 then .s8
  else if sel 9 = 1 then .s9
  else if sel 10 = 1 then .cons
  else .s0

theorem algebraMap_eq_one_iff (x : F) : algebraMap F K x = 1 ↔ x = 1 := by
  constructor
  · intro h; apply (algebraMap F K).injective; rw [h, map_one]
  · intro h; rw [h, map_one]

/-- **The decoded state is a function of the base selectors.** -/
theorem computeStateOf_decodeSource (env : CorrectedFinalTypedEnv F K) :
    StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource env) =
      stateOfBase (fun k => if h : k < 13 then env.baseTrace ⟨k, h⟩ else 0) := by
  have ht : ∀ k (hk : k < 11), (StrategyOfTracesLift.decodeSource env).trace k =
      algebraMap F K (env.baseTrace ⟨k, by omega⟩) := by
    intro k hk
    simp [StrategyOfTracesLift.decodeSource, Env.ofSubst, OptimizedComputeSubstitution.computeSubst,
      OptimizedComputeSubstitution.computeTraceSubst, hk, Expr.eval,
      CorrectedFinalTypedEnv.toSourceEnv, show k < 13 by omega]
  unfold StrategyOfTracesLift.computeStateOf stateOfBase
  simp only [ht 1 (by norm_num), ht 2 (by norm_num), ht 3 (by norm_num), ht 4 (by norm_num),
    ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num), ht 8 (by norm_num),
    ht 9 (by norm_num), ht 10 (by norm_num), algebraMap_eq_one_iff]
  simp only [show (1 : ℕ) < 13 by norm_num, show (2 : ℕ) < 13 by norm_num,
    show (3 : ℕ) < 13 by norm_num, show (4 : ℕ) < 13 by norm_num, show (5 : ℕ) < 13 by norm_num,
    show (6 : ℕ) < 13 by norm_num, show (7 : ℕ) < 13 by norm_num, show (8 : ℕ) < 13 by norm_num,
    show (9 : ℕ) < 13 by norm_num, show (10 : ℕ) < 13 by norm_num, dite_true]


/-- The decoded label of a compute row (`StrategyOfTracesLift`'s `lblCAt` body). -/
def rowLabel (env : CorrectedFinalTypedEnv F K) : State × DTcomp K :=
  let st := StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource env)
  (st, (StrategyOfTracesLift.decodeInputs env, StrategyOfTracesLift.decodePub env st,
    StrategyOfTracesLift.decodeDec env))

/-- The round-0 carrier of a compute row. -/
def rowCarrier (env : CorrectedFinalTypedEnv F K) : ℕ :=
  RecordCarrier.natLift (algebraMap F K env.expCol)

/-- 1-indexed row data with `lblC`'s off-range convention (row `1`). -/
def at1 {N : ℕ} {α : Type*} (hN : 0 < N) (f : Fin N → α) (i : ℕ) : α :=
  if h : i - 1 < N then f ⟨i - 1, h⟩ else f ⟨0, hN⟩

theorem rowLabel_fst (env : CorrectedFinalTypedEnv F K) :
    (rowLabel env).1 = stateOfBase (fun k => if h : k < 13 then env.baseTrace ⟨k, h⟩ else 0) :=
  computeStateOf_decodeSource env

/-- **The walk instance's compute tree** over a row family. -/
def computeTree {N : ℕ} (hN : 0 < N) (envs : Fin N → CorrectedFinalTypedEnv F K) :
    NTree ((State × DTcomp K) × ℕ) :=
  treeOfRows (at1 hN fun i => (rowLabel (envs i)).1) (at1 hN fun i => (rowLabel (envs i)).2)
    (at1 hN fun i => rowCarrier (envs i)) N

/-- **Its shape**, read from the base selectors and the carrier. -/
def computeShape {N : ℕ} (hN : 0 < N) (envs : Fin N → CorrectedFinalTypedEnv F K) :
    NTree (State × ℕ) :=
  shapeOfRows (at1 hN fun i => stateOfBase (fun k => if h : k < 13 then (envs i).baseTrace ⟨k, h⟩ else 0))
    (at1 hN fun i => rowCarrier (envs i)) N

theorem computeTree_shape {N : ℕ} (hN : 0 < N) (envs : Fin N → CorrectedFinalTypedEnv F K) :
    shapeOfTree (computeTree hN envs) = computeShape hN envs := by
  unfold computeTree computeShape
  rw [tree_shape]
  congr 1
  funext i
  unfold at1
  split_ifs <;> simp only [rowLabel_fst]

theorem computeShape_size_le {N : ℕ} (hN : 0 < N) (envs : Fin N → CorrectedFinalTypedEnv F K) :
    (computeShape hN envs).size ≤ N :=
  shapeOfRows_size_le _ _ _ hN

end Decode

/-! ## 3. The shape is B0 at the 309 table -/

/-- The 309 table's base selector columns `0 … 10` and the carrier column `302` are round 0. -/
theorem shape_cols_round0 :
    (∀ k < 13, RepartitionedStaging.newComputeColRound k = 0) ∧
      RepartitionedStaging.newComputeColRound 302 = 0 := by
  refine ⟨fun k hk => ?_, by decide⟩
  unfold RepartitionedStaging.newComputeColRound
  rw [if_pos hk]

end

end Nock.NockVMROM.Thm54.SVWalk
