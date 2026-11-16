/-
  Nock/NockVMROM/Thm54/P8Core/Batch1021Thm54C2JoinAssembly.lean

  The
  remaining declarations stay in `Nock/RedTeam/Batch1021Thm54C2JoinAssembly.lean`, which imports this module. This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`. -/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
import Nock.NockVMROM.Thm54.P8Core.Batch525Thm54ComputeTreeBinds

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1021

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch525
open Nock.GlobalCarryRecognizer
open scoped Polynomial
open Polynomial
variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
/-- The C2 join on the S-carrying exec tree, at the served lookup `sv` and the axes `ax`. -/
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

theorem J_cons {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .cons) :
    J (n + 1) (.node row [c0, c1]) subj formula =
      let k0 := J n c0 subj (nounHead formula)
      let k1 := J n c1 subj (nounTail formula)
      .node (c2SkeletonRow sv ax .cons row.2 subj formula [k0.label, k1.label])
        [k0, k1] := by
  simp [c2JoinFuel, hstate]

theorem J_s1 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (hstate : row.1.1 = .s1) :
    J (n + 1) (.node row []) subj formula =
      .node (c2SkeletonRow sv ax .s1 row.2 subj formula []) [] := by
  simp [c2JoinFuel, hstate]

theorem J_s0 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (hstate : row.1.1 = .s0) :
    J (n + 1) (.node row []) subj formula =
      .node (c2SkeletonRow sv ax .s0 row.2 subj formula []) [] := by
  simp [c2JoinFuel, hstate]

theorem J_subject (fuel : ℕ)
    (t : NTree ((State × DTcomp K) × ℕ)) (subj formula : Noun) :
    (J fuel t subj formula).label.subject = subj := by
  cases fuel <;> cases t <;> rfl

theorem J_formula (fuel : ℕ)
    (t : NTree ((State × DTcomp K) × ℕ)) (subj formula : Noun) :
    (J fuel t subj formula).label.formula = formula := by
  cases fuel <;> cases t <;> rfl

theorem c2SkeletonRow_eq_skelCons
    (S : ℕ)
    (subj fh ft : Noun) 
    (k0 k1 : ComputeRowSkeleton)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = fh)
    (hk1s : k1.subject = subj) (hk1f : k1.formula = ft) :
    c2SkeletonRow sv ax .cons S subj (.cell fh ft) [k0, k1] =
      skelCons subj fh ft k0.evaluation k1.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, skelCons, kidSkel,
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
theorem computeTreeBinds_join_cons {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj fh ft : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .cons)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .cons)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hfh : bindFP z fh row.1.2.2.2.f_h)
    (hft : bindFP z ft row.1.2.2.2.f_t)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hk0s : (J n c0 subj fh).label.subject = subj)
    (hk0f : (J n c0 subj fh).label.formula = fh)
    (hk1s : (J n c1 subj ft).label.subject = subj)
    (hk1f : (J n c1 subj ft).label.formula = ft)
    (heL : bindFP z
      (J n c0 subj fh).label.evaluation
      row.1.2.2.1.sf1_e)
    (heR : bindFP z
      (J n c1 subj ft).label.evaluation
      row.1.2.2.1.sf2_e)
    (hL : ComputeTreeBinds z
      (J n c0 subj fh) (mapNTree Prod.fst c0))
    (hR : ComputeTreeBinds z
      (J n c1 subj ft) (mapNTree Prod.fst c1)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1])
        subj (.cell fh ft))
      (mapNTree Prod.fst (.node row [c0, c1])) := by
  have hunf := J_cons (sv := sv) (ax := ax) (n := n)
    subj (.cell fh ft) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := c2SkeletonRow_eq_skelCons (sv := sv) (ax := ax) row.2 subj fh ft
    (J n c0 subj fh).label
    (J n c1 subj ft).label
    hk0s hk0f hk1s hk1f
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_cons hz subj fh ft
    (J n c0 subj fh).label.evaluation
    (J n c1 subj ft).label.evaluation
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1)
    (J n c0 subj fh)
    (J n c1 subj ft)
    hstate hzRow hpubSt hs hfh hft heL heR hV hL hR

theorem c2SkeletonRow_eq_skelOp1
    (S : ℕ)
    (subj tail : Noun) :
    c2SkeletonRow sv ax .s1 S subj (.cell (.atom 1) tail) [] =
      skelOp1 subj tail := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp1, nounHead, nounTail]
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

theorem computeTreeBinds_join_op1 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj tail : Noun) (row : (State × DTcomp K) × ℕ)
    (hstate : row.1.1 = .s1)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s1)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 1) row.1.2.2.2.f_h)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [])
        subj (.cell (.atom 1) tail))
      (mapNTree Prod.fst (.node row [])) := by
  rw [J_s1 (hstate := hstate)]
  rw [c2SkeletonRow_eq_skelOp1 (sv := sv) (ax := ax) row.2 subj tail]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op1 hz subj tail row.1 hstate hzRow hpubSt hs hh ht hV

theorem J_s3 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s3) :
    J (n + 1) (.node row [c0]) subj formula =
      let k0 := J n c0 subj (nounTail formula)
      .node (c2SkeletonRow sv ax .s3 row.2 subj formula [k0.label]) [k0] := by
  simp [c2JoinFuel, hstate]

theorem J_s4 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s4) :
    J (n + 1) (.node row [c0]) subj formula =
      let k0 := J n c0 subj (nounTail formula)
      .node (c2SkeletonRow sv ax .s4 row.2 subj formula [k0.label]) [k0] := by
  simp [c2JoinFuel, hstate]

theorem c2SkeletonRow_eq_skelOp3
    (S : ℕ)
    (subj tail callResult : Noun)
    (k0 : ComputeRowSkeleton)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = tail)
    (hke : k0.evaluation = callResult) :
    c2SkeletonRow sv ax .s3 S subj (.cell (.atom 3) tail) [k0] =
      skelOp3 subj tail callResult := by
  subst hke
  simp only [c2SkeletonRow, c2Evaluation, skelOp3, kidSkel,
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

theorem computeTreeBinds_join_op3 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj tail : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s3)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s3)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 3) row.1.2.2.2.f_h)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (hcall : bindFP z
      (J n c0 subj tail).label.evaluation
      row.1.2.2.1.sf1_e)
    (hwin : OpcodeSemantics.SizeWindow z
      (J n c0 subj tail).label.evaluation)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hk0s : (J n c0 subj tail).label.subject = subj)
    (hk0f : (J n c0 subj tail).label.formula = tail)
    (hC : ComputeTreeBinds z
      (J n c0 subj tail) (mapNTree Prod.fst c0)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0])
        subj (.cell (.atom 3) tail))
      (mapNTree Prod.fst (.node row [c0])) := by
  have hunf := J_s3 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 3) tail) row c0 hstate
  rw [hunf]
  simp only [nounTail]
  have heq := c2SkeletonRow_eq_skelOp3 (sv := sv) (ax := ax) row.2 subj tail
    (J n c0 subj tail).label.evaluation
    (J n c0 subj tail).label
    hk0s hk0f rfl
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op3 hz subj tail
    (J n c0 subj tail).label.evaluation
    row.1 (mapNTree Prod.fst c0) (J n c0 subj tail)
    hstate hzRow hpubSt hs hh ht hcall hwin hV hC

theorem c2SkeletonRow_eq_skelOp4
    (S : ℕ)
    (subj tail : Noun) (k : ℕ)
    (k0 : ComputeRowSkeleton)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = tail)
    (hke : k0.evaluation = .atom k) :
    c2SkeletonRow sv ax .s4 S subj (.cell (.atom 4) tail) [k0] =
      skelOp4 subj tail (.atom k) (.atom (k + 1)) := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp4, kidSkel,
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

theorem computeTreeBinds_join_op4 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj tail : Noun) (k : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s4)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s4)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 4) row.1.2.2.2.f_h)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (hcall : bindFP z (.atom k) row.1.2.2.1.sf1_e)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hk0s : (J n c0 subj tail).label.subject = subj)
    (hk0f : (J n c0 subj tail).label.formula = tail)
    (hke : (J n c0 subj tail).label.evaluation =
      .atom k)
    (hC : ComputeTreeBinds z
      (J n c0 subj tail) (mapNTree Prod.fst c0)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0])
        subj (.cell (.atom 4) tail))
      (mapNTree Prod.fst (.node row [c0])) := by
  have hunf := J_s4 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 4) tail) row c0 hstate
  rw [hunf]
  simp only [nounTail]
  have heq := c2SkeletonRow_eq_skelOp4 (sv := sv) (ax := ax) row.2 subj tail k
    (J n c0 subj tail).label
    hk0s hk0f hke
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op4 hz subj tail k row.1 (mapNTree Prod.fst c0)
    (J n c0 subj tail)
    hstate hzRow hpubSt hs hh ht hcall hV hC

theorem c2SkeletonRow_eq_skelOp0
    (S : ℕ)
    (subj tail : Noun) :
    c2SkeletonRow sv ax .s0 S subj (.cell (.atom 0) tail) [] =
      skelOp0 subj tail (sv .verify_child (S + 2))
        (ax (S + 2)) := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp0, nounHead, nounTail]
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

theorem computeTreeBinds_join_op0 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj tail : Noun) (row : (State × DTcomp K) × ℕ)
    (hstate : row.1.1 = .s0)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s0)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 0) row.1.2.2.2.f_h)
    (ht : bindFP z tail row.1.2.2.2.f_t)
    (he : bindFP z (sv .verify_child (row.2 + 2))
      row.1.2.2.1.e)
    (hax : ((ax (row.2 + 2) : ℕ) : K) = row.1.2.2.2.f_t.leaf)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [])
        subj (.cell (.atom 0) tail))
      (mapNTree Prod.fst (.node row [])) := by
  rw [J_s0 (hstate := hstate)]
  rw [c2SkeletonRow_eq_skelOp0 (sv := sv) (ax := ax) row.2 subj tail]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op0 hz subj tail
    (sv .verify_child (row.2 + 2))
    (ax (row.2 + 2))
    row.1 hstate hzRow hpubSt hs hh ht he hax hV

theorem J_s5 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s5) :
    J (n + 1) (.node row [c0, c1]) subj formula =
      let k0 := J n c0 subj
        (nounHead (nounTail formula))
      let k1 := J n c1 subj
        (nounTail (nounTail formula))
      .node (c2SkeletonRow sv ax .s5 row.2 subj formula [k0.label, k1.label])
        [k0, k1] := by
  simp [c2JoinFuel, hstate]

theorem J_s2 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s2) :
    J (n + 1) (.node row [c0, c1, c2]) subj formula =
      let k0 := J n c0 subj
        (nounHead (nounTail formula))
      let k1 := J n c1 subj
        (nounTail (nounTail formula))
      let k2 := J n c2
        k0.label.evaluation k1.label.evaluation
      .node (c2SkeletonRow sv ax .s2 row.2 subj formula
        [k0.label, k1.label, k2.label]) [k0, k1, k2] := by
  simp [c2JoinFuel, hstate]

theorem J_s6 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s6) :
    J (n + 1) (.node row [c0, c1]) subj formula =
      let fth := nounHead (nounTail formula)
      let ftth := nounHead (nounTail (nounTail formula))
      let fttt := nounTail (nounTail (nounTail formula))
      let sCond := J n c1 subj fth
      let b :=
        match sCond.label.evaluation with
        | .atom k => k
        | _ => 0
      let sTaken := J n c0 subj
        (if b = 0 then ftth else fttt)
      .node (c2SkeletonRow sv ax .s6 row.2 subj formula
        [sTaken.label, sCond.label]) [sTaken, sCond] := by
  simp [c2JoinFuel, hstate]
  constructor <;> congr

theorem J_s7 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s7) :
    J (n + 1) (.node row [c0, c1]) subj formula =
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := J n c1 subj fth
      let sCons := J n c0 sHelp.label.evaluation ftt
      .node (c2SkeletonRow sv ax .s7 row.2 subj formula
        [sCons.label, sHelp.label]) [sCons, sHelp] := by
  simp [c2JoinFuel, hstate]

theorem J_s8 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s8) :
    J (n + 1) (.node row [c0, c1]) subj formula =
      let fth := nounHead (nounTail formula)
      let ftt := nounTail (nounTail formula)
      let sHelp := J n c1 subj fth
      let sCons := J n c0
        (Noun.cell sHelp.label.evaluation subj) ftt
      .node (c2SkeletonRow sv ax .s8 row.2 subj formula
        [sCons.label, sHelp.label]) [sCons, sHelp] := by
  simp [c2JoinFuel, hstate]

theorem J_s9 {n : ℕ}
    (subj formula : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s9) :
    J (n + 1) (.node row [c0, c1]) subj formula =
      let coreF := nounTail (nounTail formula)
      let sCore := J n c0 subj coreF
      let arm := sv .verify_child (row.2 + 3)
      let sInv := J n c1 sCore.label.evaluation arm
      .node (c2SkeletonRow sv ax .s9 row.2 subj formula
        [sCore.label, sInv.label]) [sCore, sInv] := by
  simp [c2JoinFuel, hstate]

theorem c2SkeletonRow_eq_skelOp5
    (S : ℕ)
    (subj fth ftt : Noun)
    (k0 k1 : ComputeRowSkeleton)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = fth)
    (hk1s : k1.subject = subj) (hk1f : k1.formula = ftt) :
    c2SkeletonRow sv ax .s5 S subj (.cell (.atom 5) (.cell fth ftt))
      [k0, k1] =
      skelOp5 subj fth ftt k0.evaluation k1.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp5, kidSkel,
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
    (subj fth ftt : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s5)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s5)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 5) row.1.2.2.2.f_h)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (heL : bindFP z
      (J n c0 subj fth).label.evaluation
      row.1.2.2.1.sf1_e)
    (heR : bindFP z
      (J n c1 subj ftt).label.evaluation
      row.1.2.2.1.sf2_e)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : OpcodeSemantics.PairFaithful z q
      (J n c0 subj fth).label.evaluation
      (J n c1 subj ftt).label.evaluation)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hL : ComputeTreeBinds z
      (J n c0 subj fth) (mapNTree Prod.fst c0))
    (hR : ComputeTreeBinds z
      (J n c1 subj ftt) (mapNTree Prod.fst c1)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1])
        subj (.cell (.atom 5) (.cell fth ftt)))
      (mapNTree Prod.fst (.node row [c0, c1])) := by
  have hunf := J_s5 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 5) (.cell fth ftt)) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := c2SkeletonRow_eq_skelOp5 (sv := sv) (ax := ax) row.2 subj fth ftt
    (J n c0 subj fth).label
    (J n c1 subj ftt).label
    (J_subject n c0 subj fth)
    (J_formula n c0 subj fth)
    (J_subject n c1 subj ftt)
    (J_formula n c1 subj ftt)
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op5 hz subj fth ftt
    (J n c0 subj fth).label.evaluation
    (J n c1 subj ftt).label.evaluation
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1)
    (J n c0 subj fth)
    (J n c1 subj ftt)
    hstate hzRow hpubSt hs hh hth htt heL heR hcast hfaith hV hL hR

theorem c2SkeletonRow_eq_skelOp2
    (S : ℕ)
    (subj fth ftt : Noun)
    (k0 k1 k2 : ComputeRowSkeleton)
    (hk0s : k0.subject = subj) (hk0f : k0.formula = fth)
    (hk1s : k1.subject = subj) (hk1f : k1.formula = ftt)
    (hk2s : k2.subject = k0.evaluation) (hk2f : k2.formula = k1.evaluation) :
    c2SkeletonRow sv ax .s2 S subj (.cell (.atom 2) (.cell fth ftt))
      [k0, k1, k2] =
      skelOp2 subj fth ftt k0.evaluation k1.evaluation k2.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp2, kidSkel,
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

theorem computeTreeBinds_join_op2 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj fth ftt : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 c2 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s2)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s2)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 2) row.1.2.2.2.f_h)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (he1 : bindFP z
      (J n c0 subj fth).label.evaluation
      row.1.2.2.1.sf1_e)
    (he2 : bindFP z
      (J n c1 subj ftt).label.evaluation
      row.1.2.2.1.sf2_e)
    (heApp : bindFP z
      (J n c2
        (J n c0 subj fth).label.evaluation
        (J n c1 subj ftt).label.evaluation).label.evaluation
      row.1.2.2.1.sf3_e)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (h1 : ComputeTreeBinds z
      (J n c0 subj fth) (mapNTree Prod.fst c0))
    (h2 : ComputeTreeBinds z
      (J n c1 subj ftt) (mapNTree Prod.fst c1))
    (h3 : ComputeTreeBinds z
      (J n c2
        (J n c0 subj fth).label.evaluation
        (J n c1 subj ftt).label.evaluation) (mapNTree Prod.fst c2)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1, c2])
        subj (.cell (.atom 2) (.cell fth ftt)))
      (mapNTree Prod.fst (.node row [c0, c1, c2])) := by
  have hunf := J_s2 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 2) (.cell fth ftt)) row c0 c1 c2 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := c2SkeletonRow_eq_skelOp2 (sv := sv) (ax := ax) row.2 subj fth ftt
    (J n c0 subj fth).label
    (J n c1 subj ftt).label
    (J n c2
      (J n c0 subj fth).label.evaluation
      (J n c1 subj ftt).label.evaluation).label
    (J_subject n c0 subj fth)
    (J_formula n c0 subj fth)
    (J_subject n c1 subj ftt)
    (J_formula n c1 subj ftt)
    (J_subject n c2
      (J n c0 subj fth).label.evaluation
      (J n c1 subj ftt).label.evaluation)
    (J_formula n c2
      (J n c0 subj fth).label.evaluation
      (J n c1 subj ftt).label.evaluation)
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op2 hz subj fth ftt
    (J n c0 subj fth).label.evaluation
    (J n c1 subj ftt).label.evaluation
    (J n c2
      (J n c0 subj fth).label.evaluation
      (J n c1 subj ftt).label.evaluation).label.evaluation
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1) (mapNTree Prod.fst c2)
    (J n c0 subj fth)
    (J n c1 subj ftt)
    (J n c2
      (J n c0 subj fth).label.evaluation
      (J n c1 subj ftt).label.evaluation)
    hstate hzRow hpubSt hs hh hth htt he1 he2 heApp hV h1 h2 h3

theorem c2SkeletonRow_eq_skelOp6
    (S : ℕ)
    (subj fth ftth fttt : Noun) (b : ℕ)
    (kTaken kCond : ComputeRowSkeleton)
    (hkTs : kTaken.subject = subj)
    (hkTf : kTaken.formula = if b = 0 then ftth else fttt)
    (hkCs : kCond.subject = subj) (hkCf : kCond.formula = fth)
    (hkCe : kCond.evaluation = .atom b) :
    c2SkeletonRow sv ax .s6 S subj
      (.cell (.atom 6) (.cell fth (.cell ftth fttt))) [kTaken, kCond] =
      skelOp6 subj fth ftth fttt b kTaken.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp6, kidSkel,
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

theorem computeTreeBinds_join_op6 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj fth ftth fttt : Noun) (b : ℕ) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s6)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s6)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 6) row.1.2.2.2.f_h)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htth : bindFP z ftth row.1.2.2.2.f_tth)
    (httt : bindFP z fttt row.1.2.2.2.f_ttt)
    (hb : b = 0 ∨ b = 1)
    (hcondE : (J n c1 subj fth).label.evaluation =
      .atom b)
    (hcond : bindFP z (.atom b) row.1.2.2.1.sf2_e)
    (heTaken : bindFP z
      (J n c0 subj
        (if b = 0 then ftth else fttt)).label.evaluation
      row.1.2.2.1.sf1_e)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hT : ComputeTreeBinds z
      (J n c0 subj
        (if b = 0 then ftth else fttt)) (mapNTree Prod.fst c0))
    (hC : ComputeTreeBinds z
      (J n c1 subj fth) (mapNTree Prod.fst c1)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1])
        subj (.cell (.atom 6) (.cell fth (.cell ftth fttt))))
      (mapNTree Prod.fst (.node row [c0, c1])) := by
  have hunf := J_s6 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 6) (.cell fth (.cell ftth fttt))) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail, hcondE]
  have heq := c2SkeletonRow_eq_skelOp6 (sv := sv) (ax := ax) row.2 subj fth ftth fttt b
    (J n c0 subj
      (if b = 0 then ftth else fttt)).label
    (J n c1 subj fth).label
    (J_subject n c0 subj
      (if b = 0 then ftth else fttt))
    (J_formula n c0 subj
      (if b = 0 then ftth else fttt))
    (J_subject n c1 subj fth)
    (J_formula n c1 subj fth)
    hcondE
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op6 hz subj fth ftth fttt b
    (J n c0 subj
      (if b = 0 then ftth else fttt)).label.evaluation
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1)
    (J n c0 subj
      (if b = 0 then ftth else fttt))
    (J n c1 subj fth)
    hstate hzRow hpubSt hs hh hth htth httt hb hcond heTaken hV hT hC

theorem c2SkeletonRow_eq_skelOp7
    (S : ℕ)
    (subj fth ftt : Noun)
    (kCons kHelp : ComputeRowSkeleton)
    (hkCs : kCons.subject = kHelp.evaluation) (hkCf : kCons.formula = ftt)
    (hkHs : kHelp.subject = subj) (hkHf : kHelp.formula = fth) :
    c2SkeletonRow sv ax .s7 S subj (.cell (.atom 7) (.cell fth ftt))
      [kCons, kHelp] =
      skelOp7 subj fth ftt kHelp.evaluation kCons.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp7, kidSkel,
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

theorem computeTreeBinds_join_op7 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj fth ftt : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s7)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s7)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 7) row.1.2.2.2.f_h)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (heHelp : bindFP z
      (J n c1 subj fth).label.evaluation
      row.1.2.2.1.sf2_e)
    (heCons : bindFP z
      (J n c0
        (J n c1 subj fth).label.evaluation
        ftt).label.evaluation
      row.1.2.2.1.sf1_e)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hCons : ComputeTreeBinds z
      (J n c0
        (J n c1 subj fth).label.evaluation ftt) (mapNTree Prod.fst c0))
    (hHelp : ComputeTreeBinds z
      (J n c1 subj fth) (mapNTree Prod.fst c1)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1])
        subj (.cell (.atom 7) (.cell fth ftt)))
      (mapNTree Prod.fst (.node row [c0, c1])) := by
  have hunf := J_s7 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 7) (.cell fth ftt)) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := c2SkeletonRow_eq_skelOp7 (sv := sv) (ax := ax) row.2 subj fth ftt
    (J n c0
      (J n c1 subj fth).label.evaluation ftt).label
    (J n c1 subj fth).label
    (J_subject n c0
      (J n c1 subj fth).label.evaluation ftt)
    (J_formula n c0
      (J n c1 subj fth).label.evaluation ftt)
    (J_subject n c1 subj fth)
    (J_formula n c1 subj fth)
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op7 hz subj fth ftt
    (J n c1 subj fth).label.evaluation
    (J n c0
      (J n c1 subj fth).label.evaluation ftt).label.evaluation
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1)
    (J n c0
      (J n c1 subj fth).label.evaluation ftt)
    (J n c1 subj fth)
    hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hCons hHelp

theorem c2SkeletonRow_eq_skelOp8
    (S : ℕ)
    (subj fth ftt : Noun)
    (kCons kHelp : ComputeRowSkeleton)
    (hkCs : kCons.subject = .cell kHelp.evaluation subj)
    (hkCf : kCons.formula = ftt)
    (hkHs : kHelp.subject = subj) (hkHf : kHelp.formula = fth) :
    c2SkeletonRow sv ax .s8 S subj (.cell (.atom 8) (.cell fth ftt))
      [kCons, kHelp] =
      skelOp8 subj fth ftt kHelp.evaluation kCons.evaluation := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp8, kidSkel,
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

theorem computeTreeBinds_join_op8 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj fth ftt : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s8)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s8)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 8) row.1.2.2.2.f_h)
    (hth : bindFP z fth row.1.2.2.2.f_th)
    (htt : bindFP z ftt row.1.2.2.2.f_tt)
    (heHelp : bindFP z
      (J n c1 subj fth).label.evaluation
      row.1.2.2.1.sf2_e)
    (heCons : bindFP z
      (J n c0
        (.cell (J n c1 subj fth).label.evaluation
          subj) ftt).label.evaluation
      row.1.2.2.1.sf1_e)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hCons : ComputeTreeBinds z
      (J n c0
        (.cell (J n c1 subj fth).label.evaluation
          subj) ftt) (mapNTree Prod.fst c0))
    (hHelp : ComputeTreeBinds z
      (J n c1 subj fth) (mapNTree Prod.fst c1)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1])
        subj (.cell (.atom 8) (.cell fth ftt)))
      (mapNTree Prod.fst (.node row [c0, c1])) := by
  have hunf := J_s8 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 8) (.cell fth ftt)) row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := c2SkeletonRow_eq_skelOp8 (sv := sv) (ax := ax) row.2 subj fth ftt
    (J n c0
      (.cell (J n c1 subj fth).label.evaluation
        subj) ftt).label
    (J n c1 subj fth).label
    (J_subject n c0
      (.cell (J n c1 subj fth).label.evaluation
        subj) ftt)
    (J_formula n c0
      (.cell (J n c1 subj fth).label.evaluation
        subj) ftt)
    (J_subject n c1 subj fth)
    (J_formula n c1 subj fth)
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op8 hz subj fth ftt
    (J n c1 subj fth).label.evaluation
    (J n c0
      (.cell (J n c1 subj fth).label.evaluation
        subj) ftt).label.evaluation
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1)
    (J n c0
      (.cell (J n c1 subj fth).label.evaluation
        subj) ftt)
    (J n c1 subj fth)
    hstate hzRow hpubSt hs hh hth htt heHelp heCons hV hCons hHelp

theorem c2SkeletonRow_eq_skelOp9
    (S : ℕ)
    (subj coreF arm : Noun)
    (kCore kInv : ComputeRowSkeleton)
    (hk0s : kCore.subject = subj) (hk0f : kCore.formula = coreF)
    (hk1s : kInv.subject = kCore.evaluation) (hk1f : kInv.formula = arm) :
    c2SkeletonRow sv ax .s9 S subj
      (.cell (.atom 9) (.cell (.atom (ax (S + 3))) coreF))
      [kCore, kInv] =
      skelOp9 subj coreF arm kCore.evaluation kInv.evaluation
        (ax (S + 3)) := by
  simp only [c2SkeletonRow, c2Evaluation, skelOp9, kidSkel,
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

theorem computeTreeBinds_join_op9 {z : K} (hz : z ≠ 0) {n : ℕ}
    (subj coreF : Noun) (row : (State × DTcomp K) × ℕ)
    (c0 c1 : NTree ((State × DTcomp K) × ℕ))
    (hstate : row.1.1 = .s9)
    (hzRow : row.1.2.1.z = z)
    (hpubSt : row.1.2.2.1.state = .s9)
    (hs : bindFP z subj row.1.2.2.1.s)
    (hh : bindFP z (.atom 9) row.1.2.2.2.f_h)
    (hax : bindFP z
      (.atom (ax (row.2 + 3))) row.1.2.2.2.f_th)
    (hcoreF : bindFP z coreF row.1.2.2.2.f_tt)
    (harm : bindFP z (sv .verify_child (row.2 + 3))
      row.1.2.2.1.sf2_f)
    (heCore : bindFP z
      (J n c0 subj coreF).label.evaluation
      row.1.2.2.1.sf1_e)
    (heInv : bindFP z
      (J n c1
        (J n c0 subj coreF).label.evaluation
        (sv .verify_child (row.2 + 3))).label.evaluation
      row.1.2.2.1.sf2_e)
    (haxK : ((ax (row.2 + 3) : ℕ) : K) =
      row.1.2.2.2.f_th.leaf)
    (hV : Vcomp row.1.2.1 row.1.2.2.1 row.1.2.2.2)
    (hCore : ComputeTreeBinds z
      (J n c0 subj coreF) (mapNTree Prod.fst c0))
    (hInv : ComputeTreeBinds z
      (J n c1
        (J n c0 subj coreF).label.evaluation
        (sv .verify_child (row.2 + 3))) (mapNTree Prod.fst c1)) :
    ComputeTreeBinds z
      (J (n + 1) (.node row [c0, c1])
        subj (.cell (.atom 9)
          (.cell (.atom (ax (row.2 + 3))) coreF)))
      (mapNTree Prod.fst (.node row [c0, c1])) := by
  have hunf := J_s9 (sv := sv) (ax := ax) (n := n)
    subj (.cell (.atom 9)
      (.cell (.atom (ax (row.2 + 3))) coreF))
    row c0 c1 hstate
  rw [hunf]
  simp only [nounHead, nounTail]
  have heq := c2SkeletonRow_eq_skelOp9 (sv := sv) (ax := ax) row.2 subj coreF
    (sv .verify_child (row.2 + 3))
    (J n c0 subj coreF).label
    (J n c1
      (J n c0 subj coreF).label.evaluation
      (sv .verify_child (row.2 + 3))).label
    (J_subject n c0 subj coreF)
    (J_formula n c0 subj coreF)
    (J_subject n c1
      (J n c0 subj coreF).label.evaluation
      (sv .verify_child (row.2 + 3)))
    (J_formula n c1
      (J n c0 subj coreF).label.evaluation
      (sv .verify_child (row.2 + 3)))
  rw [heq]
  simp only [mapNTree, List.map_cons, List.map_nil]
  exact computeTreeBinds_op9 hz subj coreF
    (sv .verify_child (row.2 + 3))
    (J n c0 subj coreF).label.evaluation
    (J n c1
      (J n c0 subj coreF).label.evaluation
      (sv .verify_child (row.2 + 3))).label.evaluation
    (ax (row.2 + 3))
    row.1 (mapNTree Prod.fst c0) (mapNTree Prod.fst c1)
    (J n c0 subj coreF)
    (J n c1
      (J n c0 subj coreF).label.evaluation
      (sv .verify_child (row.2 + 3)))
    hstate hzRow hpubSt hs hh hax hcoreF harm heCore heInv haxK hV hCore hInv

theorem ntree_size_pos {α : Type*} (t : NTree α) : 1 ≤ t.size := by
  cases t
  simp [NTree.size]

theorem child_size_le_of_node {α : Type*} {row : α}
    {ch : List (NTree α)} {c : NTree α} {k : ℕ}
    (hk : (NTree.node row ch).size ≤ k + 1) (hc : c ∈ ch) :
    c.size ≤ k := by
  have hsz : (NTree.node row ch).size = 1 + (ch.map NTree.size).sum := by
    simp [NTree.size]
  have hmem : c.size ∈ ch.map NTree.size := List.mem_map.mpr ⟨c, hc, rfl⟩
  have : c.size ≤ (ch.map NTree.size).sum := List.le_sum_of_mem hmem
  omega

theorem J_succ_eq :
    ∀ (k : ℕ) (t : NTree ((State × DTcomp K) × ℕ)) (subj formula : Noun),
      t.size ≤ k →
      J (k + 1) t subj formula =
        J k t subj formula := by
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
          simp [c2JoinFuel]
          cases row.1.1 <;>
            cases ch with
            | nil => simp [c2JoinFuel]
            | cons c0 ch1 =>
                cases ch1 with
                | nil =>
                    simp [c2JoinFuel]
                    try rw [ih c0 _ _ (hch c0 (by simp))]
                    trivial
                | cons c1 ch2 =>
                    cases ch2 with
                    | nil =>
                        have h0 := fun s f => ih c0 s f (hch c0 (by simp))
                        have h1 := fun s f => ih c1 s f (hch c1 (by simp))
                        simp [c2JoinFuel, c2JoinKids, h0, h1]
                    | cons c2 ch3 =>
                        cases ch3 with
                        | nil =>
                            simp [c2JoinFuel]
                            try rw [ih c0 _ _ (hch c0 (by simp))]
                            try rw [ih c1 _ _ (hch c1 (by simp))]
                            try rw [ih c2 _ _ (hch c2 (by simp))]
                            trivial
                        | cons head tail =>
                            simp [c2JoinFuel]
                            have hrew :
                                ∀ c ∈ c0 :: c1 :: c2 :: head :: tail,
                                  J (k + 1) c
                                    subj formula =
                                    J k c
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
                                (c2SkeletonRow sv ax _ row.2 subj formula)
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

theorem J_eq_of_le
    (t : NTree ((State × DTcomp K) × ℕ)) (subj formula : Noun) {n fuel : ℕ}
    (hn : t.size ≤ n) (hfuel : n ≤ fuel) :
    J fuel t subj formula =
      J n t subj formula :=
  Nat.le_induction rfl
    (fun m hm ih =>
      (J_succ_eq m t subj formula
        (Nat.le_trans hn hm)).trans ih)
    fuel hfuel

variable [Fintype K] [CharP K (ringChar K)]

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

end Nock.RedTeam.Batch1021
