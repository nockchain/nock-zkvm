/-
  Nock/RedTeam/Batch530Thm54ComputeTreeBindsDeployed.lean

`mapComputeJoinInFuel` passes `(s,f)` down the reconstructed tree
  (`rebuildForest` / `reconTree` labels): formula heads/tails, sibling
  results for OP2/7/8/9.  `ComputeTreeBinds` of
  that join against the same exec tree is the induction in this file.
  `V_comp` determines every child noun the lemmas consume.

  -- the paper
-/
import Nock.NockVMROM.Thm54.StrategyOfTraces
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVM
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn
import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.RedTeam.Batch525Thm54ComputeTreeBinds
import Nock.NockVMROM.Thm54.P8Core.Batch530Thm54ComputeTreeBindsDeployed

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch530

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.ExecOfTraces
open scoped Polynomial
open Polynomial
open Nock.RedTeam.Batch525
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.GlobalCarryRecognizer

variable {K : Type} [Field K] [DecidableEq K]

/-! ## §A  `joinNoun` of atom-shaped fingerprints -/

theorem joinNoun_atom (q : ℕ) (z : K)
    (forest : List (NTree (MState × DTmem K))) (fp : FP K)
    (h : fp.size = z ∧ fp.dyck = 0) :
    joinNoun q z forest fp = Noun.atom (leafAtomOf q fp.leaf) := by
  simp [joinNoun, h]

theorem bindFP_joinNoun_atom {q : ℕ} {z : K}
    (forest : List (NTree (MState × DTmem K))) {fp : FP K}
    (hshape : fp.size = z ∧ fp.dyck = 0)
    (hwin : ∃ k : ℕ, k < q ∧ (k : K) = fp.leaf) :
    bindFP z (joinNoun q z forest fp) fp := by
  rw [joinNoun_atom q z forest fp hshape, bindFP, enc_atom]
  apply FP.ext
  · simp [FP.atomFP]
    exact hshape.1
  · simp [FP.atomFP]
    exact hshape.2
  · simp [FP.atomFP]
    exact (leafAtomOf_cast hwin).symm

theorem atomFP_shape (z : K) (v : K) :
    (FP.atomFP z v).size = z ∧ (FP.atomFP z v).dyck = 0 := by
  simp [FP.atomFP]

theorem bindFP_joinNoun_atomFP {q : ℕ} {z : K}
    (forest : List (NTree (MState × DTmem K))) {k : ℕ}
    (hk : k < q) :
    bindFP z (joinNoun q z forest (FP.atomFP z (k : K)))
      (FP.atomFP z (k : K)) :=
  bindFP_joinNoun_atom forest (atomFP_shape z (k : K))
    ⟨k, hk, by simp [FP.atomFP]⟩

/-! ## §B  Fuel unfolding at a cons node -/

theorem mapComputeJoinInFuel_cons {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .cons) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1]) subj formula =
      let k0 := mapComputeJoinInFuel n q forest c0 subj (nounHead formula)
      let k1 := mapComputeJoinInFuel n q forest c1 subj (nounTail formula)
      .node (computeSkeletonRow q forest subj formula row [k0.label, k1.label])
        [k0, k1] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s1 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (hstate : row.1 = .s1) :
    mapComputeJoinInFuel (n + 1) q forest (.node row []) subj formula =
      .node (computeSkeletonRow q forest subj formula row []) [] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s0 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (hstate : row.1 = .s0) :
    mapComputeJoinInFuel (n + 1) q forest (.node row []) subj formula =
      .node (computeSkeletonRow q forest subj formula row []) [] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_subject (fuel q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    (mapComputeJoinInFuel fuel q forest t subj formula).label.subject = subj := by
  cases fuel <;> cases t <;> rfl

theorem mapComputeJoinInFuel_formula (fuel q : ℕ)
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) :
    (mapComputeJoinInFuel fuel q forest t subj formula).label.formula = formula := by
  cases fuel <;> cases t <;> rfl

theorem computeSkeletonRow_eq_skelCons
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj fh ft : Noun) (row : State × DTcomp K)
    (k0 k1 : ComputeRowSkeleton)
    (hstate : row.1 = .cons)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = fh)
    (hk1s : k1.subject = subj) (hk1f : k1.formula = ft) :
    computeSkeletonRow q forest subj (.cell fh ft) row [k0, k1] =
      skelCons subj fh ft k0.evaluation k1.evaluation := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelCons, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    fin_cases i
    · simp [hk0s, hk0f]
      cases slot <;> rfl
    · simp [hk1s, hk1f]
      cases slot <;> rfl
    · simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp [Nock.Framework.recordCount] at this
    · simp [Nock.Framework.recordCount] at this

/-- Cons step of the deployed join: children already bound, parent is
    `skelCons` of the passed `(s,f)` and child evaluations. -/
theorem computeTreeBinds_join_cons {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj fh ft : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .cons)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .cons)
    (hs : bindFP z subj row.2.2.1.s)
    (hfh : bindFP z fh row.2.2.2.f_h)
    (hft : bindFP z ft row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hk0s : (mapComputeJoinInFuel n q forest c0 subj fh).label.subject = subj)
    (hk0f : (mapComputeJoinInFuel n q forest c0 subj fh).label.formula = fh)
    (hk1s : (mapComputeJoinInFuel n q forest c1 subj ft).label.subject = subj)
    (hk1f : (mapComputeJoinInFuel n q forest c1 subj ft).label.formula = ft)
    (heL : bindFP z
      (mapComputeJoinInFuel n q forest c0 subj fh).label.evaluation
      row.2.2.1.sf1_e)
    (heR : bindFP z
      (mapComputeJoinInFuel n q forest c1 subj ft).label.evaluation
      row.2.2.1.sf2_e)
    (hL : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj fh) c0)
    (hR : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1 subj ft) c1) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1])
        subj (.cell fh ft))
      (.node row [c0, c1]) := by
  have hunf := mapComputeJoinInFuel_cons (n := n) (q := q) forest
    subj (.cell fh ft) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := computeSkeletonRow_eq_skelCons q forest subj fh ft row
    (mapComputeJoinInFuel n q forest c0 subj fh).label
    (mapComputeJoinInFuel n q forest c1 subj ft).label
    hstate hk0s hk0f hk1s hk1f
  rw [heq]
  exact computeTreeBinds_cons hz subj fh ft
    (mapComputeJoinInFuel n q forest c0 subj fh).label.evaluation
    (mapComputeJoinInFuel n q forest c1 subj ft).label.evaluation
    row c0 c1
    (mapComputeJoinInFuel n q forest c0 subj fh)
    (mapComputeJoinInFuel n q forest c1 subj ft)
    hstate hzRow hpubSt hs hfh hft heL heR hV hL hR

theorem computeSkeletonRow_eq_skelOp1
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (row : State × DTcomp K)
    (hstate : row.1 = .s1) :
    computeSkeletonRow q forest subj (.cell (.atom 1) tail) row [] =
      skelOp1 subj tail := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp1, joinEvaluation, nounHead, nounTail]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp [Nock.Framework.recordCount] at this
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op1 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (row : State × DTcomp K)
    (hstate : row.1 = .s1)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s1)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 1) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [])
        subj (.cell (.atom 1) tail))
      (.node row []) := by
  rw [mapComputeJoinInFuel_s1 (hstate := hstate)]
  rw [computeSkeletonRow_eq_skelOp1 q forest subj tail row hstate]
  exact computeTreeBinds_op1 hz subj tail row hstate hzRow hpubSt hs hh ht hV

theorem mapComputeJoinInFuel_s3 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 : NTree (State × DTcomp K))
    (hstate : row.1 = .s3) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0]) subj formula =
      let k0 := mapComputeJoinInFuel n q forest c0 subj (nounTail formula)
      .node (computeSkeletonRow q forest subj formula row [k0.label]) [k0] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s4 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 : NTree (State × DTcomp K))
    (hstate : row.1 = .s4) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0]) subj formula =
      let k0 := mapComputeJoinInFuel n q forest c0 subj (nounTail formula)
      .node (computeSkeletonRow q forest subj formula row [k0.label]) [k0] := by
  simp [mapComputeJoinInFuel, hstate]

theorem computeSkeletonRow_eq_skelOp3
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj tail callResult : Noun) (row : State × DTcomp K)
    (k0 : ComputeRowSkeleton)
    (hstate : row.1 = .s3)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = tail)
    (hke : k0.evaluation = callResult) :
    computeSkeletonRow q forest subj (.cell (.atom 3) tail) row [k0] =
      skelOp3 subj tail callResult := by
  cases row
  subst hstate
  subst hke
  simp only [computeSkeletonRow, skelOp3, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    have : (i : ℕ) < 1 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hk0s, hk0f]
      cases slot <;> rfl
    · simp [fanoutComp] at this
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp [Nock.Framework.recordCount] at this
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op3 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (row : State × DTcomp K)
    (c0 : NTree (State × DTcomp K))
    (hstate : row.1 = .s3)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s3)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 3) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hcall : bindFP z
      (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation
      row.2.2.1.sf1_e)
    (hwin : OpcodeSemantics.SizeWindow z
      (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hk0s : (mapComputeJoinInFuel n q forest c0 subj tail).label.subject = subj)
    (hk0f : (mapComputeJoinInFuel n q forest c0 subj tail).label.formula = tail)
    (hC : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj tail) c0) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0])
        subj (.cell (.atom 3) tail))
      (.node row [c0]) := by
  have hunf := mapComputeJoinInFuel_s3 (n := n) (q := q) forest
    subj (.cell (.atom 3) tail) row c0 hstate
  rw [hunf]
  simp only [nounTail]
  have heq := computeSkeletonRow_eq_skelOp3 q forest subj tail
    (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation row
    (mapComputeJoinInFuel n q forest c0 subj tail).label
    hstate hk0s hk0f rfl
  rw [heq]
  exact computeTreeBinds_op3 hz subj tail
    (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation
    row c0 (mapComputeJoinInFuel n q forest c0 subj tail)
    hstate hzRow hpubSt hs hh ht hcall hwin hV hC

theorem computeSkeletonRow_eq_skelOp4
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (k : ℕ) (row : State × DTcomp K)
    (k0 : ComputeRowSkeleton)
    (hstate : row.1 = .s4)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = tail)
    (hke : k0.evaluation = .atom k) :
    computeSkeletonRow q forest subj (.cell (.atom 4) tail) row [k0] =
      skelOp4 subj tail (.atom k) (.atom (k + 1)) := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp4, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero, Option.getD, hke]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    have : (i : ℕ) < 1 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hk0s, hk0f]
      cases slot <;> first | rfl | exact hke
    · simp [fanoutComp] at this
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 1 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · simp [Nock.Framework.recordCount] at this
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op4 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (k : ℕ) (row : State × DTcomp K)
    (c0 : NTree (State × DTcomp K))
    (hstate : row.1 = .s4)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s4)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 4) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hcall : bindFP z (.atom k) row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hk0s : (mapComputeJoinInFuel n q forest c0 subj tail).label.subject = subj)
    (hk0f : (mapComputeJoinInFuel n q forest c0 subj tail).label.formula = tail)
    (hke : (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation =
      .atom k)
    (hC : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj tail) c0) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0])
        subj (.cell (.atom 4) tail))
      (.node row [c0]) := by
  have hunf := mapComputeJoinInFuel_s4 (n := n) (q := q) forest
    subj (.cell (.atom 4) tail) row c0 hstate
  rw [hunf]
  simp only [nounTail]
  have heq := computeSkeletonRow_eq_skelOp4 q forest subj tail k row
    (mapComputeJoinInFuel n q forest c0 subj tail).label
    hstate hk0s hk0f hke
  rw [heq]
  exact computeTreeBinds_op4 hz subj tail k row c0
    (mapComputeJoinInFuel n q forest c0 subj tail)
    hstate hzRow hpubSt hs hh ht hcall hV hC

/-! ## §B.2  s0 / s2 / s5–s9 -/

theorem computeSkeletonRow_eq_skelOp0
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (row : State × DTcomp K)
    (hstate : row.1 = .s0) :
    computeSkeletonRow q forest subj (.cell (.atom 0) tail) row [] =
      skelOp0 subj tail (StrategyOfTraces.nounByFP q forest row.2.2.1.e)
        (leafAtomOf q row.2.2.2.f_t.leaf) := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp0, joinEvaluation, nounHead, nounTail,
    StrategyOfTraces.nounByFP]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t => rfl
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [decActive, hasTailDecomposition] at hact
  · funext i hi slot
    simp [fanoutComp] at hi
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op0 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj tail : Noun) (row : State × DTcomp K)
    (hstate : row.1 = .s0)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s0)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 0) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (he : bindFP z (StrategyOfTraces.nounByFP q forest row.2.2.1.e)
      row.2.2.1.e)
    (hax : ((leafAtomOf q row.2.2.2.f_t.leaf : ℕ) : K) = row.2.2.2.f_t.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [])
        subj (.cell (.atom 0) tail))
      (.node row []) := by
  rw [mapComputeJoinInFuel_s0 (hstate := hstate)]
  rw [computeSkeletonRow_eq_skelOp0 q forest subj tail row hstate]
  exact computeTreeBinds_op0 hz subj tail
    (StrategyOfTraces.nounByFP q forest row.2.2.1.e)
    (leafAtomOf q row.2.2.2.f_t.leaf)
    row hstate hzRow hpubSt hs hh ht he hax hV

theorem mapComputeJoinInFuel_s5 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s5) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1]) subj formula =
      let k0 := mapComputeJoinInFuel n q forest c0 subj
        (nounHead (nounTail formula))
      let k1 := mapComputeJoinInFuel n q forest c1 subj
        (nounTail (nounTail formula))
      .node (computeSkeletonRow q forest subj formula row [k0.label, k1.label])
        [k0, k1] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s2 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 c2 : NTree (State × DTcomp K))
    (hstate : row.1 = .s2) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1, c2]) subj formula =
      let k0 := mapComputeJoinInFuel n q forest c0 subj
        (nounHead (nounTail formula))
      let k1 := mapComputeJoinInFuel n q forest c1 subj
        (nounTail (nounTail formula))
      let k2 := mapComputeJoinInFuel n q forest c2
        k0.label.evaluation k1.label.evaluation
      .node (computeSkeletonRow q forest subj formula row
        [k0.label, k1.label, k2.label]) [k0, k1, k2] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s6 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s6) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1]) subj formula =
      let fth := nounHead (nounTail formula)
      let ftth := nounHead (nounTail (nounTail formula))
      let fttt := nounTail (nounTail (nounTail formula))
      let sCond := mapComputeJoinInFuel n q forest c1 subj fth
      let b :=
        match sCond.label.evaluation with
        | .atom k => k
        | _ => 0
      let sTaken := mapComputeJoinInFuel n q forest c0 subj
        (if b = 0 then ftth else fttt)
      .node (computeSkeletonRow q forest subj formula row
        [sTaken.label, sCond.label]) [sTaken, sCond] := by
  simp [mapComputeJoinInFuel, hstate]
  constructor <;> congr

theorem mapComputeJoinInFuel_s7 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s7) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1]) subj formula =
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := mapComputeJoinInFuel n q forest c1 subj fth
      let sCons := mapComputeJoinInFuel n q forest c0 sHelp.label.evaluation ftt
      .node (computeSkeletonRow q forest subj formula row
        [sCons.label, sHelp.label]) [sCons, sHelp] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s8 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s8) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1]) subj formula =
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := mapComputeJoinInFuel n q forest c1 subj fth
      let sCons := mapComputeJoinInFuel n q forest c0
        (Noun.cell sHelp.label.evaluation subj) ftt
      .node (computeSkeletonRow q forest subj formula row
        [sCons.label, sHelp.label]) [sCons, sHelp] := by
  simp [mapComputeJoinInFuel, hstate]

theorem mapComputeJoinInFuel_s9 {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj formula : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s9) :
    mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1]) subj formula =
      let coreF := nounTail (nounTail formula)
      let sCore := mapComputeJoinInFuel n q forest c0 subj coreF
      let arm := joinNoun q row.2.1.z forest row.2.2.1.sf2_f
      let sInv := mapComputeJoinInFuel n q forest c1 sCore.label.evaluation arm
      .node (computeSkeletonRow q forest subj formula row
        [sCore.label, sInv.label]) [sCore, sInv] := by
  simp [mapComputeJoinInFuel, hstate]

theorem computeSkeletonRow_eq_skelOp5
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (k0 k1 : ComputeRowSkeleton)
    (hstate : row.1 = .s5)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = fth)
    (hk1s : k1.subject = subj) (hk1f : k1.formula = ftt) :
    computeSkeletonRow q forest subj (.cell (.atom 5) (.cell fth ftt)) row
      [k0, k1] =
      skelOp5 subj fth ftt k0.evaluation k1.evaluation := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp5, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt =>
        simp [decActive] at hact
  · funext i hi slot
    have : (i : ℕ) < 2 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hk0s, hk0f]
      cases slot <;> rfl
    · simp [hk1s, hk1f]
      cases slot <;> rfl
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op5 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s5)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s5)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 5) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heL : bindFP z
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      row.2.2.1.sf1_e)
    (heR : bindFP z
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation
      row.2.2.1.sf2_e)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : OpcodeSemantics.PairFaithful z q
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hL : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj fth) c0)
    (hR : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1 subj ftt) c1) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1])
        subj (.cell (.atom 5) (.cell fth ftt)))
      (.node row [c0, c1]) := by
  have hunf := mapComputeJoinInFuel_s5 (n := n) (q := q) forest
    subj (.cell (.atom 5) (.cell fth ftt)) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := computeSkeletonRow_eq_skelOp5 q forest subj fth ftt row
    (mapComputeJoinInFuel n q forest c0 subj fth).label
    (mapComputeJoinInFuel n q forest c1 subj ftt).label
    hstate (mapComputeJoinInFuel_subject n q forest c0 subj fth)
    (mapComputeJoinInFuel_formula n q forest c0 subj fth)
    (mapComputeJoinInFuel_subject n q forest c1 subj ftt)
    (mapComputeJoinInFuel_formula n q forest c1 subj ftt)
  rw [heq]
  exact computeTreeBinds_op5 hz subj fth ftt
    (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
    (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation
    row c0 c1
    (mapComputeJoinInFuel n q forest c0 subj fth)
    (mapComputeJoinInFuel n q forest c1 subj ftt)
    hstate hzRow hpubSt hs hh hth htt heL heR hcast hfaith hV hL hR

theorem computeSkeletonRow_eq_skelOp2
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (k0 k1 k2 : ComputeRowSkeleton)
    (hstate : row.1 = .s2)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = fth)
    (hk1s : k1.subject = subj) (hk1f : k1.formula = ftt)
    (hk2s : k2.subject = k0.evaluation) (hk2f : k2.formula = k1.evaluation) :
    computeSkeletonRow q forest subj (.cell (.atom 2) (.cell fth ftt)) row
      [k0, k1, k2] =
      skelOp2 subj fth ftt k0.evaluation k1.evaluation k2.evaluation := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp2, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt =>
        simp [decActive] at hact
  · funext i hi slot
    have : (i : ℕ) < 3 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hk0s, hk0f]
      cases slot <;> rfl
    · simp [hk1s, hk1f]
      cases slot <;> rfl
    · simp [hk2s, hk2f]
      cases slot <;> rfl
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op2 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (c0 c1 c2 : NTree (State × DTcomp K))
    (hstate : row.1 = .s2)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s2)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 2) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (he1 : bindFP z
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      row.2.2.1.sf1_e)
    (he2 : bindFP z
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation
      row.2.2.1.sf2_e)
    (heApp : bindFP z
      (mapComputeJoinInFuel n q forest c2
        (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
        (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation).label.evaluation
      row.2.2.1.sf3_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (h1 : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj fth) c0)
    (h2 : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1 subj ftt) c1)
    (h3 : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c2
        (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
        (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation) c2) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1, c2])
        subj (.cell (.atom 2) (.cell fth ftt)))
      (.node row [c0, c1, c2]) := by
  have hunf := mapComputeJoinInFuel_s2 (n := n) (q := q) forest
    subj (.cell (.atom 2) (.cell fth ftt)) row c0 c1 c2 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := computeSkeletonRow_eq_skelOp2 q forest subj fth ftt row
    (mapComputeJoinInFuel n q forest c0 subj fth).label
    (mapComputeJoinInFuel n q forest c1 subj ftt).label
    (mapComputeJoinInFuel n q forest c2
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation).label
    hstate
    (mapComputeJoinInFuel_subject n q forest c0 subj fth)
    (mapComputeJoinInFuel_formula n q forest c0 subj fth)
    (mapComputeJoinInFuel_subject n q forest c1 subj ftt)
    (mapComputeJoinInFuel_formula n q forest c1 subj ftt)
    (mapComputeJoinInFuel_subject n q forest c2
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation)
    (mapComputeJoinInFuel_formula n q forest c2
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation)
  rw [heq]
  exact computeTreeBinds_op2 hz subj fth ftt
    (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
    (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation
    (mapComputeJoinInFuel n q forest c2
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation).label.evaluation
    row c0 c1 c2
    (mapComputeJoinInFuel n q forest c0 subj fth)
    (mapComputeJoinInFuel n q forest c1 subj ftt)
    (mapComputeJoinInFuel n q forest c2
      (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation)
    hstate hzRow hpubSt hs hh hth htt he1 he2 heApp hV h1 h2 h3

theorem computeSkeletonRow_eq_skelOp6
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj fth ftth fttt : Noun) (b : ℕ) (row : State × DTcomp K)
    (kTaken kCond : ComputeRowSkeleton)
    (hstate : row.1 = .s6)
    (hkTs : kTaken.subject = subj)
    (hkTf : kTaken.formula = if b = 0 then ftth else fttt)
    (hkCs : kCond.subject = subj) (hkCf : kCond.formula = fth)
    (hkCe : kCond.evaluation = .atom b) :
    computeSkeletonRow q forest subj
      (.cell (.atom 6) (.cell fth (.cell ftth fttt))) row [kTaken, kCond] =
      skelOp6 subj fth ftth fttt b kTaken.evaluation := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp6, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt | .f_tth | .f_ttt => rfl
  · funext i hi slot
    have : (i : ℕ) < 2 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hkTs, hkTf]
      cases slot <;> rfl
    · simp [hkCs, hkCf, hkCe]
      cases slot <;> first | rfl | exact hkCe
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 3 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · rfl

theorem computeTreeBinds_join_op6 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj fth ftth fttt : Noun) (b : ℕ) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s6)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s6)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 6) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htth : bindFP z ftth row.2.2.2.f_tth)
    (httt : bindFP z fttt row.2.2.2.f_ttt)
    (hb : b = 0 ∨ b = 1)
    (hcondE : (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation =
      .atom b)
    (hcond : bindFP z (.atom b) row.2.2.1.sf2_e)
    (heTaken : bindFP z
      (mapComputeJoinInFuel n q forest c0 subj
        (if b = 0 then ftth else fttt)).label.evaluation
      row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hT : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj
        (if b = 0 then ftth else fttt)) c0)
    (hC : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1 subj fth) c1) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1])
        subj (.cell (.atom 6) (.cell fth (.cell ftth fttt))))
      (.node row [c0, c1]) := by
  have hunf := mapComputeJoinInFuel_s6 (n := n) (q := q) forest
    subj (.cell (.atom 6) (.cell fth (.cell ftth fttt))) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail, hcondE]
  have heq := computeSkeletonRow_eq_skelOp6 q forest subj fth ftth fttt b row
    (mapComputeJoinInFuel n q forest c0 subj
      (if b = 0 then ftth else fttt)).label
    (mapComputeJoinInFuel n q forest c1 subj fth).label
    hstate
    (mapComputeJoinInFuel_subject n q forest c0 subj
      (if b = 0 then ftth else fttt))
    (mapComputeJoinInFuel_formula n q forest c0 subj
      (if b = 0 then ftth else fttt))
    (mapComputeJoinInFuel_subject n q forest c1 subj fth)
    (mapComputeJoinInFuel_formula n q forest c1 subj fth)
    hcondE
  rw [heq]
  exact computeTreeBinds_op6 hz subj fth ftth fttt b
    (mapComputeJoinInFuel n q forest c0 subj
      (if b = 0 then ftth else fttt)).label.evaluation
    row c0 c1
    (mapComputeJoinInFuel n q forest c0 subj
      (if b = 0 then ftth else fttt))
    (mapComputeJoinInFuel n q forest c1 subj fth)
    hstate hzRow hpubSt hs hh hth htth httt hb hcond heTaken hV hT hC

theorem computeSkeletonRow_eq_skelOp7
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (kCons kHelp : ComputeRowSkeleton)
    (hstate : row.1 = .s7)
    (hkCs : kCons.subject = kHelp.evaluation) (hkCf : kCons.formula = ftt)
    (hkHs : kHelp.subject = subj) (hkHf : kHelp.formula = fth) :
    computeSkeletonRow q forest subj (.cell (.atom 7) (.cell fth ftt)) row
      [kCons, kHelp] =
      skelOp7 subj fth ftt kHelp.evaluation kCons.evaluation := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp7, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt =>
        simp [decActive] at hact
  · funext i hi slot
    have : (i : ℕ) < 2 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hkCs, hkCf]
      cases slot <;> rfl
    · simp [hkHs, hkHf]
      cases slot <;> rfl
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op7 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s7)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s7)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 7) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heHelp : bindFP z
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
      row.2.2.1.sf2_e)
    (heCons : bindFP z
      (mapComputeJoinInFuel n q forest c0
        (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
        ftt).label.evaluation
      row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hCons : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0
        (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation ftt) c0)
    (hHelp : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1 subj fth) c1) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1])
        subj (.cell (.atom 7) (.cell fth ftt)))
      (.node row [c0, c1]) := by
  have hunf := mapComputeJoinInFuel_s7 (n := n) (q := q) forest
    subj (.cell (.atom 7) (.cell fth ftt)) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := computeSkeletonRow_eq_skelOp7 q forest subj fth ftt row
    (mapComputeJoinInFuel n q forest c0
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation ftt).label
    (mapComputeJoinInFuel n q forest c1 subj fth).label
    hstate
    (mapComputeJoinInFuel_subject n q forest c0
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation ftt)
    (mapComputeJoinInFuel_formula n q forest c0
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation ftt)
    (mapComputeJoinInFuel_subject n q forest c1 subj fth)
    (mapComputeJoinInFuel_formula n q forest c1 subj fth)
  rw [heq]
  exact computeTreeBinds_op7 hz subj fth ftt
    (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
    (mapComputeJoinInFuel n q forest c0
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation ftt).label.evaluation
    row c0 c1
    (mapComputeJoinInFuel n q forest c0
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation ftt)
    (mapComputeJoinInFuel n q forest c1 subj fth)
    hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hCons hHelp

theorem computeSkeletonRow_eq_skelOp8
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (kCons kHelp : ComputeRowSkeleton)
    (hstate : row.1 = .s8)
    (hkCs : kCons.subject = .cell kHelp.evaluation subj)
    (hkCf : kCons.formula = ftt)
    (hkHs : kHelp.subject = subj) (hkHf : kHelp.formula = fth) :
    computeSkeletonRow q forest subj (.cell (.atom 8) (.cell fth ftt)) row
      [kCons, kHelp] =
      skelOp8 subj fth ftt kHelp.evaluation kCons.evaluation := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp8, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt =>
        simp [decActive] at hact
  · funext i hi slot
    have : (i : ℕ) < 2 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hkCs, hkCf]
      cases slot <;> rfl
    · simp [hkHs, hkHf]
      cases slot <;> rfl
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 2 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp [Nock.Framework.recordCount] at this

theorem computeTreeBinds_join_op8 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj fth ftt : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s8)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s8)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 8) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heHelp : bindFP z
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
      row.2.2.1.sf2_e)
    (heCons : bindFP z
      (mapComputeJoinInFuel n q forest c0
        (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
          subj) ftt).label.evaluation
      row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hCons : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0
        (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
          subj) ftt) c0)
    (hHelp : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1 subj fth) c1) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1])
        subj (.cell (.atom 8) (.cell fth ftt)))
      (.node row [c0, c1]) := by
  have hunf := mapComputeJoinInFuel_s8 (n := n) (q := q) forest
    subj (.cell (.atom 8) (.cell fth ftt)) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := computeSkeletonRow_eq_skelOp8 q forest subj fth ftt row
    (mapComputeJoinInFuel n q forest c0
      (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
        subj) ftt).label
    (mapComputeJoinInFuel n q forest c1 subj fth).label
    hstate
    (mapComputeJoinInFuel_subject n q forest c0
      (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
        subj) ftt)
    (mapComputeJoinInFuel_formula n q forest c0
      (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
        subj) ftt)
    (mapComputeJoinInFuel_subject n q forest c1 subj fth)
    (mapComputeJoinInFuel_formula n q forest c1 subj fth)
  rw [heq]
  exact computeTreeBinds_op8 hz subj fth ftt
    (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
    (mapComputeJoinInFuel n q forest c0
      (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
        subj) ftt).label.evaluation
    row c0 c1
    (mapComputeJoinInFuel n q forest c0
      (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
        subj) ftt)
    (mapComputeJoinInFuel n q forest c1 subj fth)
    hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hCons hHelp

theorem computeSkeletonRow_eq_skelOp9
    (q : ℕ) (forest : List (NTree (MState × DTmem K)))
    (subj coreF arm : Noun) (row : State × DTcomp K)
    (kCore kInv : ComputeRowSkeleton)
    (hstate : row.1 = .s9)
    (hk0s : kCore.subject = subj) (hk0f : kCore.formula = coreF)
    (hk1s : kInv.subject = kCore.evaluation) (hk1f : kInv.formula = arm) :
    computeSkeletonRow q forest subj
      (.cell (.atom 9) (.cell (.atom (leafAtomOf q row.2.2.2.f_th.leaf)) coreF))
      row [kCore, kInv] =
      skelOp9 subj coreF arm kCore.evaluation kInv.evaluation
        (leafAtomOf q row.2.2.2.f_th.leaf) := by
  cases row
  subst hstate
  simp only [computeSkeletonRow, skelOp9, joinEvaluation, kidSkel,
    nounHead, nounTail, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD]
  congr 1
  · funext slot hact
    match slot with
    | .f_h | .f_t | .f_th | .f_tt => rfl
    | .f_tth | .f_ttt =>
        simp [decActive] at hact
  · funext i hi slot
    have : (i : ℕ) < 2 := by simpa [fanoutComp] using hi
    fin_cases i
    · simp [hk0s, hk0f]
      cases slot <;> rfl
    · simp [hk1s, hk1f]
      cases slot <;> rfl
    · simp [fanoutComp] at this
  · funext i hi
    have : (i : ℕ) < 3 := by simpa [Nock.Framework.recordCount] using hi
    fin_cases i
    · rfl
    · rfl
    · simp [hk0s, hk1f]

theorem computeTreeBinds_join_op9 {z : K} (hz : z ≠ 0) {n q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (subj coreF : Noun) (row : State × DTcomp K)
    (c0 c1 : NTree (State × DTcomp K))
    (hstate : row.1 = .s9)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s9)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 9) row.2.2.2.f_h)
    (hax : bindFP z
      (.atom (leafAtomOf q row.2.2.2.f_th.leaf)) row.2.2.2.f_th)
    (hcoreF : bindFP z coreF row.2.2.2.f_tt)
    (harm : bindFP z (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)
      row.2.2.1.sf2_f)
    (heCore : bindFP z
      (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
      row.2.2.1.sf1_e)
    (heInv : bindFP z
      (mapComputeJoinInFuel n q forest c1
        (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
        (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)).label.evaluation
      row.2.2.1.sf2_e)
    (haxK : ((leafAtomOf q row.2.2.2.f_th.leaf : ℕ) : K) =
      row.2.2.2.f_th.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hCore : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c0 subj coreF) c0)
    (hInv : ComputeTreeBinds z
      (mapComputeJoinInFuel n q forest c1
        (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
        (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)) c1) :
    ComputeTreeBinds z
      (mapComputeJoinInFuel (n + 1) q forest (.node row [c0, c1])
        subj (.cell (.atom 9)
          (.cell (.atom (leafAtomOf q row.2.2.2.f_th.leaf)) coreF)))
      (.node row [c0, c1]) := by
  have hunf := mapComputeJoinInFuel_s9 (n := n) (q := q) forest
    subj (.cell (.atom 9)
      (.cell (.atom (leafAtomOf q row.2.2.2.f_th.leaf)) coreF))
    row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := computeSkeletonRow_eq_skelOp9 q forest subj coreF
    (joinNoun q row.2.1.z forest row.2.2.1.sf2_f) row
    (mapComputeJoinInFuel n q forest c0 subj coreF).label
    (mapComputeJoinInFuel n q forest c1
      (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
      (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)).label
    hstate
    (mapComputeJoinInFuel_subject n q forest c0 subj coreF)
    (mapComputeJoinInFuel_formula n q forest c0 subj coreF)
    (mapComputeJoinInFuel_subject n q forest c1
      (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
      (joinNoun q row.2.1.z forest row.2.2.1.sf2_f))
    (mapComputeJoinInFuel_formula n q forest c1
      (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
      (joinNoun q row.2.1.z forest row.2.2.1.sf2_f))
  rw [heq]
  exact computeTreeBinds_op9 hz subj coreF
    (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)
    (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
    (mapComputeJoinInFuel n q forest c1
      (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
      (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)).label.evaluation
    (leafAtomOf q row.2.2.2.f_th.leaf)
    row c0 c1
    (mapComputeJoinInFuel n q forest c0 subj coreF)
    (mapComputeJoinInFuel n q forest c1
      (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
      (joinNoun q row.2.1.z forest row.2.2.1.sf2_f))
    hstate hzRow hpubSt hs hh hax hcoreF harm heCore heInv haxK hV hCore hInv

/-! ## §B.3  Tree induction: `ComputeJoinReady` packages per-node `V_comp` -/

/-- Per-node data `V_comp` determines plus child
    readiness.  Child evaluation `bindFP`s are derived from
    `ComputeTreeBinds.root` + `childLink` after the IH. -/
inductive ComputeJoinReady (z : K) (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) :
    NTree (State × DTcomp K) → Noun → Noun → Prop
  | op0 {row : State × DTcomp K} {subj tail : Noun}
      (hstate : row.1 = .s0)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s0)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 0) row.2.2.2.f_h)
      (ht : bindFP z tail row.2.2.2.f_t)
      (he : bindFP z (StrategyOfTraces.nounByFP q forest row.2.2.1.e)
        row.2.2.1.e)
      (hax : ((leafAtomOf q row.2.2.2.f_t.leaf : ℕ) : K) =
        row.2.2.2.f_t.leaf)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
      ComputeJoinReady z q forest (.node row []) subj (.cell (.atom 0) tail)
  | op1 {row : State × DTcomp K} {subj tail : Noun}
      (hstate : row.1 = .s1)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s1)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 1) row.2.2.2.f_h)
      (ht : bindFP z tail row.2.2.2.f_t)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
      ComputeJoinReady z q forest (.node row []) subj (.cell (.atom 1) tail)
  | cons {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
      {subj fh ft : Noun}
      (hstate : row.1 = .cons)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .cons)
      (hs : bindFP z subj row.2.2.1.s)
      (hfh : bindFP z fh row.2.2.2.f_h)
      (hft : bindFP z ft row.2.2.2.f_t)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (heLlink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (heRlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (hL : ComputeJoinReady z q forest c0 subj fh)
      (hR : ComputeJoinReady z q forest c1 subj ft) :
      ComputeJoinReady z q forest (.node row [c0, c1]) subj (.cell fh ft)
  | op3 {row : State × DTcomp K} {c0 : NTree (State × DTcomp K)}
      {subj tail : Noun}
      (hstate : row.1 = .s3)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s3)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 3) row.2.2.2.f_h)
      (ht : bindFP z tail row.2.2.2.f_t)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (hwin : ∀ n : ℕ,
        OpcodeSemantics.SizeWindow z
          (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation)
      (helink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (hC : ComputeJoinReady z q forest c0 subj tail) :
      ComputeJoinReady z q forest (.node row [c0]) subj (.cell (.atom 3) tail)
  | op4 {row : State × DTcomp K} {c0 : NTree (State × DTcomp K)}
      {subj tail : Noun} {k : ℕ}
      (hstate : row.1 = .s4)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s4)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 4) row.2.2.2.f_h)
      (ht : bindFP z tail row.2.2.2.f_t)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (hke : ∀ n : ℕ,
        (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation =
          .atom k)
      (hcall : bindFP z (.atom k) row.2.2.1.sf1_e)
      (hC : ComputeJoinReady z q forest c0 subj tail) :
      ComputeJoinReady z q forest (.node row [c0]) subj (.cell (.atom 4) tail)
  | op5 {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
      {subj fth ftt : Noun}
      (hstate : row.1 = .s5)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s5)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 5) row.2.2.2.f_h)
      (hth : bindFP z fth row.2.2.2.f_th)
      (htt : bindFP z ftt row.2.2.2.f_tt)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hfaith : ∀ n : ℕ,
        OpcodeSemantics.PairFaithful z q
          (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
          (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation)
      (heLlink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (heRlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (hL : ComputeJoinReady z q forest c0 subj fth)
      (hR : ComputeJoinReady z q forest c1 subj ftt) :
      ComputeJoinReady z q forest (.node row [c0, c1])
        subj (.cell (.atom 5) (.cell fth ftt))
  | op2 {row : State × DTcomp K}
      {c0 c1 c2 : NTree (State × DTcomp K)}
      {subj fth ftt : Noun}
      (hstate : row.1 = .s2)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s2)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 2) row.2.2.2.f_h)
      (hth : bindFP z fth row.2.2.2.f_th)
      (htt : bindFP z ftt row.2.2.2.f_tt)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (he1link : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (he2link : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (heApplink : c2.label.2.2.1.e = row.2.2.1.sf3_e)
      (h1 : ComputeJoinReady z q forest c0 subj fth)
      (h2 : ComputeJoinReady z q forest c1 subj ftt)
      (h3 : ComputeJoinReady z q forest c2
        (mapComputeJoinInFuel (c0.size) q forest c0 subj fth).label.evaluation
        (mapComputeJoinInFuel (c1.size) q forest c1 subj ftt).label.evaluation) :
      ComputeJoinReady z q forest (.node row [c0, c1, c2])
        subj (.cell (.atom 2) (.cell fth ftt))
  | op6 {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
      {subj fth ftth fttt : Noun} {b : ℕ}
      (hstate : row.1 = .s6)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s6)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 6) row.2.2.2.f_h)
      (hth : bindFP z fth row.2.2.2.f_th)
      (htth : bindFP z ftth row.2.2.2.f_tth)
      (httt : bindFP z fttt row.2.2.2.f_ttt)
      (hb : b = 0 ∨ b = 1)
      (hcondE : ∀ n : ℕ,
        (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation =
          .atom b)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (heTakenlink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (hcondlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (hT : ComputeJoinReady z q forest c0 subj
        (if b = 0 then ftth else fttt))
      (hC : ComputeJoinReady z q forest c1 subj fth) :
      ComputeJoinReady z q forest (.node row [c0, c1])
        subj (.cell (.atom 6) (.cell fth (.cell ftth fttt)))
  | op7 {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
      {subj fth ftt : Noun}
      (hstate : row.1 = .s7)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s7)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 7) row.2.2.2.f_h)
      (hth : bindFP z fth row.2.2.2.f_th)
      (htt : bindFP z ftt row.2.2.2.f_tt)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (heHelplink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (heConslink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (hHelp : ComputeJoinReady z q forest c1 subj fth)
      (hCons : ComputeJoinReady z q forest c0
        (mapComputeJoinInFuel c1.size q forest c1 subj fth).label.evaluation
        ftt) :
      ComputeJoinReady z q forest (.node row [c0, c1])
        subj (.cell (.atom 7) (.cell fth ftt))
  | op8 {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
      {subj fth ftt : Noun}
      (hstate : row.1 = .s8)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s8)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 8) row.2.2.2.f_h)
      (hth : bindFP z fth row.2.2.2.f_th)
      (htt : bindFP z ftt row.2.2.2.f_tt)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (heHelplink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (heConslink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (hHelp : ComputeJoinReady z q forest c1 subj fth)
      (hCons : ComputeJoinReady z q forest c0
        (.cell
          (mapComputeJoinInFuel c1.size q forest c1 subj fth).label.evaluation
          subj) ftt) :
      ComputeJoinReady z q forest (.node row [c0, c1])
        subj (.cell (.atom 8) (.cell fth ftt))
  | op9 {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
      {subj coreF : Noun}
      (hstate : row.1 = .s9)
      (hzRow : row.2.1.z = z)
      (hpubSt : row.2.2.1.state = .s9)
      (hs : bindFP z subj row.2.2.1.s)
      (hh : bindFP z (.atom 9) row.2.2.2.f_h)
      (hax : bindFP z (.atom (leafAtomOf q row.2.2.2.f_th.leaf))
        row.2.2.2.f_th)
      (hcoreF : bindFP z coreF row.2.2.2.f_tt)
      (harm : bindFP z (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)
        row.2.2.1.sf2_f)
      (haxK : ((leafAtomOf q row.2.2.2.f_th.leaf : ℕ) : K) =
        row.2.2.2.f_th.leaf)
      (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
      (heCorelink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
      (heInvlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
      (hCore : ComputeJoinReady z q forest c0 subj coreF)
      (hInv : ComputeJoinReady z q forest c1
        (mapComputeJoinInFuel c0.size q forest c0 subj coreF).label.evaluation
        (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)) :
      ComputeJoinReady z q forest (.node row [c0, c1])
        subj (.cell (.atom 9)
          (.cell (.atom (leafAtomOf q row.2.2.2.f_th.leaf)) coreF))

theorem mapComputeJoinInFuel_succ_eq {q : ℕ}
    (forest : List (NTree (MState × DTmem K))) :
    ∀ (k : ℕ) (t : NTree (State × DTcomp K)) (subj formula : Noun),
      t.size ≤ k →
      mapComputeJoinInFuel (k + 1) q forest t subj formula =
        mapComputeJoinInFuel k q forest t subj formula := by
  intro k
  induction k with
  | zero =>
      intro t subj formula hk
      have := ntree_size_pos t
      omega
  | succ k ih =>
      intro t subj formula hk
      cases t with
      | node row ch =>
          have hch : ∀ c ∈ ch, c.size ≤ k :=
            fun c hc => child_size_le_of_node hk hc
          simp [mapComputeJoinInFuel]
          cases row.1 <;>
            cases ch with
            | nil => simp [mapComputeJoinInFuel]
            | cons c0 ch1 =>
                cases ch1 with
                | nil =>
                    simp [mapComputeJoinInFuel]
                    try rw [ih c0 _ _ (hch c0 (by simp))]
                    trivial
                | cons c1 ch2 =>
                    cases ch2 with
                    | nil =>
                        have h0 := fun s f => ih c0 s f (hch c0 (by simp))
                        have h1 := fun s f => ih c1 s f (hch c1 (by simp))
                        simp [mapComputeJoinInFuel, mapComputeJoinKids, h0, h1]
                    | cons c2 ch3 =>
                        cases ch3 with
                        | nil =>
                            simp [mapComputeJoinInFuel]
                            try rw [ih c0 _ _ (hch c0 (by simp))]
                            try rw [ih c1 _ _ (hch c1 (by simp))]
                            try rw [ih c2 _ _ (hch c2 (by simp))]
                            trivial
                        | cons head tail =>
                            simp [mapComputeJoinInFuel]
                            have hrew :
                                ∀ c ∈ c0 :: c1 :: c2 :: head :: tail,
                                  mapComputeJoinInFuel (k + 1) q forest c
                                    subj formula =
                                    mapComputeJoinInFuel k q forest c
                                      subj formula :=
                              fun c hc => ih c subj formula (hch c hc)
                            have hmem : ∀ a ∈ tail,
                                a ∈ c0 :: c1 :: c2 :: head :: tail :=
                              fun a ha =>
                                List.mem_cons_of_mem _
                                  (List.mem_cons_of_mem _
                                    (List.mem_cons_of_mem _
                                      (List.mem_cons_of_mem _ ha)))
                            constructor
                            · rw [hrew c0 (by simp), hrew c1 (by simp),
                                hrew c2 (by simp), hrew head (by simp)]
                              apply congrArg
                                (computeSkeletonRow q forest subj formula row)
                              refine congrArg (List.cons _)
                                (congrArg (List.cons _)
                                  (congrArg (List.cons _)
                                    (congrArg (List.cons _) ?_)))
                              apply List.map_congr_left
                              intro a ha
                              simp only [Function.comp]
                              rw [hrew a (hmem a ha)]
                            · refine ⟨hrew c0 (by simp), hrew c1 (by simp),
                                hrew c2 (by simp), hrew head (by simp), ?_⟩
                              intro a ha
                              exact hrew a (hmem a ha)

theorem mapComputeJoinInFuel_eq_of_le {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (State × DTcomp K)) (subj formula : Noun) {n fuel : ℕ}
    (hn : t.size ≤ n) (hfuel : n ≤ fuel) :
    mapComputeJoinInFuel fuel q forest t subj formula =
      mapComputeJoinInFuel n q forest t subj formula :=
  Nat.le_induction rfl
    (fun m hm ih =>
      (mapComputeJoinInFuel_succ_eq forest m t subj formula
        (Nat.le_trans hn hm)).trans ih)
    fuel hfuel

theorem computeTreeBinds_of_ready {z : K} (hz : z ≠ 0) {q fuel : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {t : NTree (State × DTcomp K)} {subj formula : Noun}
    (hfuel : t.size ≤ fuel)
    (hR : ComputeJoinReady z q forest t subj formula) :
    ComputeTreeBinds z (mapComputeJoinInFuel fuel q forest t subj formula) t := by
  induction hR generalizing fuel with
  | @op0 row subj tail hstate hzRow hpubSt hs hh ht he hax hV =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact computeTreeBinds_join_op0 hz forest subj tail row hstate hzRow hpubSt
        hs hh ht he hax hV
  | @op1 row subj tail hstate hzRow hpubSt hs hh ht hV =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      exact computeTreeBinds_join_op1 hz forest subj tail row hstate hzRow hpubSt
        hs hh ht hV
  | @cons row c0 c1 subj fh ft hstate hzRow hpubSt hs hfh hft hV
      heLlink heRlink hL hR ihL ihR =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hn1 : c1.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hLb := ihL hn0
      have hRb := ihR hn1
      have heL : bindFP z
          (mapComputeJoinInFuel n q forest c0 subj fh).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hLb).2.2.2.2.2.1
        simpa [heLlink] using hb
      have heR : bindFP z
          (mapComputeJoinInFuel n q forest c1 subj ft).label.evaluation
          row.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hRb).2.2.2.2.2.1
        simpa [heRlink] using hb
      exact computeTreeBinds_join_cons hz forest subj fh ft row c0 c1
        hstate hzRow hpubSt hs hfh hft hV
        (mapComputeJoinInFuel_subject n q forest c0 subj fh)
        (mapComputeJoinInFuel_formula n q forest c0 subj fh)
        (mapComputeJoinInFuel_subject n q forest c1 subj ft)
        (mapComputeJoinInFuel_formula n q forest c1 subj ft)
        heL heR hLb hRb
  | @op3 row c0 subj tail hstate hzRow hpubSt hs hh ht hV hwin helink hC ih =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0]).size = 1 + c0.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hCb := ih hn0
      have hcall : bindFP z
          (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hCb).2.2.2.2.2.1
        simpa [helink] using hb
      exact computeTreeBinds_join_op3 hz forest subj tail row c0
        hstate hzRow hpubSt hs hh ht hcall (hwin n) hV
        (mapComputeJoinInFuel_subject n q forest c0 subj tail)
        (mapComputeJoinInFuel_formula n q forest c0 subj tail) hCb
  | @op4 row c0 subj tail k hstate hzRow hpubSt hs hh ht hV hke hcall hC ih =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0]).size = 1 + c0.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hn0 : c0.size ≤ n := by
        have := hfuel
        simp [hsz] at this
        omega
      have hCb := ih hn0
      exact computeTreeBinds_join_op4 hz forest subj tail k row c0
        hstate hzRow hpubSt hs hh ht hcall hV
        (mapComputeJoinInFuel_subject n q forest c0 subj tail)
        (mapComputeJoinInFuel_formula n q forest c0 subj tail) (hke n) hCb
  | @op5 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      hcast hfaith heLlink heRlink hL hR ihL ihR =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hLb := ihL hn0
      have hRb := ihR hn1
      have heL : bindFP z
          (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hLb).2.2.2.2.2.1
        simpa [heLlink] using hb
      have heR : bindFP z
          (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation
          row.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hRb).2.2.2.2.2.1
        simpa [heRlink] using hb
      exact computeTreeBinds_join_op5 hz forest subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heL heR hcast (hfaith n) hV hLb hRb
  | @op2 row c0 c1 c2 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      he1link he2link heApplink h1 h2 h3 ih1 ih2 ih3 =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1, c2]).size =
          1 + c0.size + c1.size + c2.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn2 : c2.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have h1b := ih1 hn0
      have h2b := ih2 hn1
      have heq0 := mapComputeJoinInFuel_eq_of_le (q := q) forest c0 subj fth
        (Nat.le_refl _) hn0
      have heq1 := mapComputeJoinInFuel_eq_of_le (q := q) forest c1 subj ftt
        (Nat.le_refl _) hn1
      have h3b := ih3 hn2
      rw [← heq0, ← heq1] at h3b
      have he1 : bindFP z
          (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root h1b).2.2.2.2.2.1
        simpa [he1link] using hb
      have he2 : bindFP z
          (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation
          row.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root h2b).2.2.2.2.2.1
        simpa [he2link] using hb
      have heApp : bindFP z
          (mapComputeJoinInFuel n q forest c2
            (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
            (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation).label.evaluation
          row.2.2.1.sf3_e := by
        have hb := (ComputeTreeBinds.root h3b).2.2.2.2.2.1
        simpa [heApplink] using hb
      exact computeTreeBinds_join_op2 hz forest subj fth ftt row c0 c1 c2
        hstate hzRow hpubSt hs hh hth htt he1 he2 heApp hV h1b h2b h3b
  | @op6 row c0 c1 subj fth ftth fttt b hstate hzRow hpubSt hs hh hth htth
      httt hb hcondE hV heTakenlink hcondlink hT hC ihT ihC =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hTb := ihT hn0
      have hCb := ihC hn1
      have hcond : bindFP z (.atom b) row.2.2.1.sf2_e := by
        have hb' := (ComputeTreeBinds.root hCb).2.2.2.2.2.1
        simpa [hcondlink, hcondE n] using hb'
      have heTaken : bindFP z
          (mapComputeJoinInFuel n q forest c0 subj
            (if b = 0 then ftth else fttt)).label.evaluation
          row.2.2.1.sf1_e := by
        have hb' := (ComputeTreeBinds.root hTb).2.2.2.2.2.1
        simpa [heTakenlink] using hb'
      exact computeTreeBinds_join_op6 hz forest subj fth ftth fttt b row c0 c1
        hstate hzRow hpubSt hs hh hth htth httt hb (hcondE n) hcond heTaken
        hV hTb hCb
  | @op7 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      heHelplink heConslink hHelp hCons ihHelp ihCons =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hHelpb := ihHelp hn1
      have heq := mapComputeJoinInFuel_eq_of_le (q := q) forest c1 subj fth
        (Nat.le_refl _) hn1
      have hConsb := ihCons hn0
      rw [← heq] at hConsb
      have heHelp : bindFP z
          (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
          row.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hHelpb).2.2.2.2.2.1
        simpa [heHelplink] using hb
      have heCons : bindFP z
          (mapComputeJoinInFuel n q forest c0
            (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
            ftt).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hConsb).2.2.2.2.2.1
        simpa [heConslink] using hb
      exact computeTreeBinds_join_op7 hz forest subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hConsb hHelpb
  | @op8 row c0 c1 subj fth ftt hstate hzRow hpubSt hs hh hth htt hV
      heHelplink heConslink hHelp hCons ihHelp ihCons =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hHelpb := ihHelp hn1
      have heq := mapComputeJoinInFuel_eq_of_le (q := q) forest c1 subj fth
        (Nat.le_refl _) hn1
      have hConsb := ihCons hn0
      rw [← heq] at hConsb
      have heHelp : bindFP z
          (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
          row.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hHelpb).2.2.2.2.2.1
        simpa [heHelplink] using hb
      have heCons : bindFP z
          (mapComputeJoinInFuel n q forest c0
            (.cell (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation
              subj) ftt).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hConsb).2.2.2.2.2.1
        simpa [heConslink] using hb
      exact computeTreeBinds_join_op8 hz forest subj fth ftt row c0 c1
        hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hConsb hHelpb
  | @op9 row c0 c1 subj coreF hstate hzRow hpubSt hs hh hax hcoreF harm haxK
      hV heCorelink heInvlink hCore hInv ihCore ihInv =>
      have hpos : 0 < fuel :=
        Nat.lt_of_lt_of_le (Nat.succ_le_iff.mp (ntree_size_pos _)) hfuel
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hsz : (NTree.node row [c0, c1]).size = 1 + c0.size + c1.size := by
        simp [NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_assoc]
      have hn0 : c0.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hn1 : c1.size ≤ n := by
        have := hfuel; simp [hsz] at this; omega
      have hCoreb := ihCore hn0
      have heq := mapComputeJoinInFuel_eq_of_le (q := q) forest c0 subj coreF
        (Nat.le_refl _) hn0
      have hInvb := ihInv hn1
      rw [← heq] at hInvb
      have heCore : bindFP z
          (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
          row.2.2.1.sf1_e := by
        have hb := (ComputeTreeBinds.root hCoreb).2.2.2.2.2.1
        simpa [heCorelink] using hb
      have heInv : bindFP z
          (mapComputeJoinInFuel n q forest c1
            (mapComputeJoinInFuel n q forest c0 subj coreF).label.evaluation
            (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)).label.evaluation
          row.2.2.1.sf2_e := by
        have hb := (ComputeTreeBinds.root hInvb).2.2.2.2.2.1
        simpa [heInvlink] using hb
      exact computeTreeBinds_join_op9 hz forest subj coreF row c0 c1
        hstate hzRow hpubSt hs hh hax hcoreF harm heCore heInv haxK hV
        hCoreb hInvb

/-! ## §C  Exec-tree join (the tree `strategyOfTraces` must bind) -/

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- Join of `execOfTraces.computeTree` — same constructor family as
    `reconTree`, so `ComputeTreeBinds` is an induction on that tree. -/
noncomputable def computeJoinOfExec
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) : ComputeJoin where
  computeTree :=
    mapComputeJoin (ringChar K) (typedMemoryForest P Qm)
      (execOfTraces P Qc Qm c h).computeTree

theorem computeJoinOfExec_tree
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (computeJoinOfExec P Qc Qm c h).computeTree =
      mapComputeJoin (ringChar K) (typedMemoryForest P Qm)
        (execOfTraces P Qc Qm c h).computeTree :=
  rfl

theorem ComputeJoinReady.label_z {z : K} {q : ℕ}
    {forest : List (NTree (MState × DTmem K))}
    {t : NTree (State × DTcomp K)} {subj formula : Noun}
    (hR : ComputeJoinReady z q forest t subj formula) :
    t.label.2.1.z = z := by
  cases hR <;> assumption

/-- `SVhead` of a non-`cons` row is `headAtom`. -/
theorem vcomp_headAtom {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K}
    (hV : Vcomp inp pub dec) (hcons : pub.state ≠ State.cons) :
    headAtom dec inp.z (pub.state.toNat : K) := by
  have hsv : SVhead inp pub dec := hV.2.2.1
  simpa [SVhead, hcons] using hsv

/-- Opcode formula-head is `atomFP z op` (`evalV` / SV4–6). -/
theorem vcomp_f_h_eq_atomFP {inp : ComputeTable.Inputs K} {pub : ComputeTable.Pub K}
    {dec : ComputeTable.Dec K}
    (hV : Vcomp inp pub dec) {op : ℕ}
    (hst : pub.state.toNat = op) (hcons : pub.state ≠ State.cons) :
    dec.f_h = FP.atomFP inp.z (op : K) := by
  have hA := vcomp_headAtom hV hcons
  apply FP.ext
  · simpa [FP.atomFP, hst] using hA.1
  · simpa [FP.atomFP] using hA.2.1
  · simpa [FP.atomFP, hst] using hA.2.2

theorem bindFP_vcomp_opcode {z : K} {inp : ComputeTable.Inputs K}
    {pub : ComputeTable.Pub K} {dec : ComputeTable.Dec K}
    (hV : Vcomp inp pub dec) (hz : inp.z = z) {op : ℕ}
    (hst : pub.state.toNat = op) (hcons : pub.state ≠ State.cons) :
    bindFP z (.atom op) dec.f_h := by
  rw [bindFP, vcomp_f_h_eq_atomFP hV hst hcons, hz, enc_atom]

/-- Child `(s,f,e)` is the parent's `sfTriple` (`childLinkComp`, `:1690`). -/
theorem fcomp_child_sfe {lbl : State × DTcomp K}
    {xout : Fin 3 → Option (State × DTcomp K)}
    (hF : Fcomp lbl xout) (i : Fin 3)
    (hi : (i : ℕ) < fanoutComp lbl.1) {c : State × DTcomp K}
    (hc : xout i = some c) :
    (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e) = sfTriple lbl.2.2.1 i := by
  have hlink := hF.2.2.2 i hi
  simpa [hc] using hlink

/-- `ComputeJoinReady` of a `s0` leaf — every noun is `V_comp`-determined. -/
theorem computeJoinReady_op0_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {subj tail : Noun}
    (hstate : row.1 = .s0)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s0)
    (hs : bindFP z subj row.2.2.1.s)
    (ht : bindFP z tail row.2.2.2.f_t)
    (he : bindFP z (StrategyOfTraces.nounByFP q forest row.2.2.1.e)
      row.2.2.1.e)
    (hax : ((leafAtomOf q row.2.2.2.f_t.leaf : ℕ) : K) =
      row.2.2.2.f_t.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeJoinReady z q forest (.node row []) subj (.cell (.atom 0) tail) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 0 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op0 hstate hzRow hpubSt hs hh ht he hax hV

/-- `ComputeJoinReady` of a `s1` leaf. -/
theorem computeJoinReady_op1_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {subj tail : Noun}
    (hstate : row.1 = .s1)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s1)
    (hs : bindFP z subj row.2.2.1.s)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeJoinReady z q forest (.node row []) subj (.cell (.atom 1) tail) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 1 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op1 hstate hzRow hpubSt hs hh ht hV

/-- `cons` packages `V_comp` plus both child `Ready`s (`evalV` `:1728-1742`). -/
theorem computeJoinReady_cons_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
    {subj fh ft : Noun}
    (hstate : row.1 = .cons)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .cons)
    (hs : bindFP z subj row.2.2.1.s)
    (hfh : bindFP z fh row.2.2.2.f_h)
    (hft : bindFP z ft row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (heLlink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (heRlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (hL : ComputeJoinReady z q forest c0 subj fh)
    (hR : ComputeJoinReady z q forest c1 subj ft) :
    ComputeJoinReady z q forest (.node row [c0, c1]) subj (.cell fh ft) :=
  ComputeJoinReady.cons hstate hzRow hpubSt hs hfh hft hV heLlink heRlink hL hR

theorem computeJoinReady_op3_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 : NTree (State × DTcomp K)}
    {subj tail : Noun}
    (hstate : row.1 = .s3)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s3)
    (hs : bindFP z subj row.2.2.1.s)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hwin : ∀ n : ℕ,
      OpcodeSemantics.SizeWindow z
        (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation)
    (helink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (hC : ComputeJoinReady z q forest c0 subj tail) :
    ComputeJoinReady z q forest (.node row [c0]) subj (.cell (.atom 3) tail) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 3 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op3 hstate hzRow hpubSt hs hh ht hV hwin helink hC

theorem computeJoinReady_op4_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 : NTree (State × DTcomp K)}
    {subj tail : Noun} {k : ℕ}
    (hstate : row.1 = .s4)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s4)
    (hs : bindFP z subj row.2.2.1.s)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hke : ∀ n : ℕ,
      (mapComputeJoinInFuel n q forest c0 subj tail).label.evaluation =
        .atom k)
    (hcall : bindFP z (.atom k) row.2.2.1.sf1_e)
    (hC : ComputeJoinReady z q forest c0 subj tail) :
    ComputeJoinReady z q forest (.node row [c0]) subj (.cell (.atom 4) tail) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 4 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op4 hstate hzRow hpubSt hs hh ht hV hke hcall hC

theorem computeJoinReady_op5_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
    {subj fth ftt : Noun}
    (hstate : row.1 = .s5)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s5)
    (hs : bindFP z subj row.2.2.1.s)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : ∀ n : ℕ,
      OpcodeSemantics.PairFaithful z q
        (mapComputeJoinInFuel n q forest c0 subj fth).label.evaluation
        (mapComputeJoinInFuel n q forest c1 subj ftt).label.evaluation)
    (heLlink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (heRlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (hL : ComputeJoinReady z q forest c0 subj fth)
    (hR : ComputeJoinReady z q forest c1 subj ftt) :
    ComputeJoinReady z q forest (.node row [c0, c1])
      subj (.cell (.atom 5) (.cell fth ftt)) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 5 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op5 hstate hzRow hpubSt hs hh hth htt hV
    hcast hfaith heLlink heRlink hL hR

theorem computeJoinReady_op2_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K}
    {c0 c1 c2 : NTree (State × DTcomp K)}
    {subj fth ftt : Noun}
    (hstate : row.1 = .s2)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s2)
    (hs : bindFP z subj row.2.2.1.s)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (he1link : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (he2link : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (heApplink : c2.label.2.2.1.e = row.2.2.1.sf3_e)
    (h1 : ComputeJoinReady z q forest c0 subj fth)
    (h2 : ComputeJoinReady z q forest c1 subj ftt)
    (h3 : ComputeJoinReady z q forest c2
      (mapComputeJoinInFuel (c0.size) q forest c0 subj fth).label.evaluation
      (mapComputeJoinInFuel (c1.size) q forest c1 subj ftt).label.evaluation) :
    ComputeJoinReady z q forest (.node row [c0, c1, c2])
      subj (.cell (.atom 2) (.cell fth ftt)) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 2 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op2 hstate hzRow hpubSt hs hh hth htt hV
    he1link he2link heApplink h1 h2 h3

theorem computeJoinReady_op6_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
    {subj fth ftth fttt : Noun} {b : ℕ}
    (hstate : row.1 = .s6)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s6)
    (hs : bindFP z subj row.2.2.1.s)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htth : bindFP z ftth row.2.2.2.f_tth)
    (httt : bindFP z fttt row.2.2.2.f_ttt)
    (hb : b = 0 ∨ b = 1)
    (hcondE : ∀ n : ℕ,
      (mapComputeJoinInFuel n q forest c1 subj fth).label.evaluation =
        .atom b)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (heTakenlink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (hcondlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (hT : ComputeJoinReady z q forest c0 subj
      (if b = 0 then ftth else fttt))
    (hC : ComputeJoinReady z q forest c1 subj fth) :
    ComputeJoinReady z q forest (.node row [c0, c1])
      subj (.cell (.atom 6) (.cell fth (.cell ftth fttt))) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 6 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op6 hstate hzRow hpubSt hs hh hth htth httt hb
    hcondE hV heTakenlink hcondlink hT hC

theorem computeJoinReady_op7_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
    {subj fth ftt : Noun}
    (hstate : row.1 = .s7)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s7)
    (hs : bindFP z subj row.2.2.1.s)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (heHelplink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (heConslink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (hHelp : ComputeJoinReady z q forest c1 subj fth)
    (hCons : ComputeJoinReady z q forest c0
      (mapComputeJoinInFuel c1.size q forest c1 subj fth).label.evaluation
      ftt) :
    ComputeJoinReady z q forest (.node row [c0, c1])
      subj (.cell (.atom 7) (.cell fth ftt)) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 7 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op7 hstate hzRow hpubSt hs hh hth htt hV
    heHelplink heConslink hHelp hCons

theorem computeJoinReady_op8_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
    {subj fth ftt : Noun}
    (hstate : row.1 = .s8)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s8)
    (hs : bindFP z subj row.2.2.1.s)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (heHelplink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (heConslink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (hHelp : ComputeJoinReady z q forest c1 subj fth)
    (hCons : ComputeJoinReady z q forest c0
      (.cell
        (mapComputeJoinInFuel c1.size q forest c1 subj fth).label.evaluation
        subj) ftt) :
    ComputeJoinReady z q forest (.node row [c0, c1])
      subj (.cell (.atom 8) (.cell fth ftt)) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 8 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op8 hstate hzRow hpubSt hs hh hth htt hV
    heHelplink heConslink hHelp hCons

theorem computeJoinReady_op9_of_vcomp {z : K} {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    {row : State × DTcomp K} {c0 c1 : NTree (State × DTcomp K)}
    {subj coreF : Noun}
    (hstate : row.1 = .s9)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s9)
    (hs : bindFP z subj row.2.2.1.s)
    (hax : bindFP z (.atom (leafAtomOf q row.2.2.2.f_th.leaf))
      row.2.2.2.f_th)
    (hcoreF : bindFP z coreF row.2.2.2.f_tt)
    (harm : bindFP z (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)
      row.2.2.1.sf2_f)
    (haxK : ((leafAtomOf q row.2.2.2.f_th.leaf : ℕ) : K) =
      row.2.2.2.f_th.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (heCorelink : c0.label.2.2.1.e = row.2.2.1.sf1_e)
    (heInvlink : c1.label.2.2.1.e = row.2.2.1.sf2_e)
    (hCore : ComputeJoinReady z q forest c0 subj coreF)
    (hInv : ComputeJoinReady z q forest c1
      (mapComputeJoinInFuel c0.size q forest c0 subj coreF).label.evaluation
      (joinNoun q row.2.1.z forest row.2.2.1.sf2_f)) :
    ComputeJoinReady z q forest (.node row [c0, c1])
      subj (.cell (.atom 9)
        (.cell (.atom (leafAtomOf q row.2.2.2.f_th.leaf)) coreF)) := by
  have hcons : row.2.2.1.state ≠ State.cons := by simp [hpubSt]
  have hst : row.2.2.1.state.toNat = 9 := by simp [hpubSt, State.toNat]
  have hh := bindFP_vcomp_opcode hV hzRow hst hcons
  exact ComputeJoinReady.op9 hstate hzRow hpubSt hs hh hax hcoreF harm haxK hV
    heCorelink heInvlink hCore hInv

/-- `ComputeTreeBinds` of the joined exec tree — induction on
    `ComputeJoinReady` (`V_comp` per node). -/
theorem ComputeTreeBindsOfExec
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) {z : K} (hz : z ≠ 0)
    (hR : ComputeJoinReady z (ringChar K) (typedMemoryForest P Qm)
      (execOfTraces P Qc Qm c h).computeTree
      (joinNoun (ringChar K) z (typedMemoryForest P Qm)
        (execOfTraces P Qc Qm c h).computeTree.label.2.2.1.s)
      (joinFormulaDeep (ringChar K) (typedMemoryForest P Qm)
        (execOfTraces P Qc Qm c h).computeTree)) :
    ComputeTreeBinds z
      (computeJoinOfExec P Qc Qm c h).computeTree
      (execOfTraces P Qc Qm c h).computeTree := by
  have hzRow := ComputeJoinReady.label_z hR
  change ComputeTreeBinds z
    (mapComputeJoin (ringChar K) (typedMemoryForest P Qm)
      (execOfTraces P Qc Qm c h).computeTree)
    _
  unfold mapComputeJoin mapComputeJoinIn
  simp only [hzRow]
  exact computeTreeBinds_of_ready hz (typedMemoryForest P Qm) (Nat.le_refl _) hR

/-- Opcode heads `0..9` sit in `[0, ringChar)` once `25 ≤ p` (`nockCompiles`
    floor).  Not a `V_comp` gap: `evalV` pins `f_h = atomFP z opcode`. -/
theorem opcode_atom_in_window {p : ℕ} (hp : 25 ≤ p) (op : ℕ) (hop : op ≤ 9) :
    op < p :=
  Nat.lt_of_le_of_lt hop (Nat.lt_of_lt_of_le (by decide : (9 : ℕ) < 25) hp)

end Nock.RedTeam.Batch530

#print axioms Nock.RedTeam.Batch530.bindFP_joinNoun_atom
#print axioms Nock.RedTeam.Batch530.mapComputeJoinInFuel_cons
#print axioms Nock.RedTeam.Batch530.computeSkeletonRow_eq_skelCons
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_cons
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op1
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op3
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op4
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op0
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op2
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op5
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op6
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op7
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op8
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_join_op9
#print axioms Nock.RedTeam.Batch530.computeTreeBinds_of_ready
#print axioms Nock.RedTeam.Batch530.ComputeTreeBindsOfExec
#print axioms Nock.RedTeam.Batch530.computeJoinOfExec_tree
#print axioms Nock.RedTeam.Batch530.bindFP_vcomp_opcode
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op0_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op1_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_cons_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op2_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op3_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op4_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op5_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op6_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op7_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op8_of_vcomp
#print axioms Nock.RedTeam.Batch530.computeJoinReady_op9_of_vcomp
