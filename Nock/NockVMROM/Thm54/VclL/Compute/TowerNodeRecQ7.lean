import Nock.NockVMROM.Thm54.VclL.Compute.TowerRowFactsQ7
import Nock.NockVMROM.Thm54.VclL.Compute.TowerReader
import Nock.NockVMROM.Thm54.VclL.Compute.TowerReqFacts
import Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7

/-!
# The tower `node_records` from tower acceptance

`node_records_Q7G` at
`G := towerGather δ V.basis`, `R := towerReader δ V.basis`, `T` any wide table (the 409-wide tower
table once it is defined), with `RF := towerRowFactsQ7` and the one-hot-state hypothesis `hrow`
discharged from the tower rows (`selAt_of_towerRow` + `rowLabel_fst_of_selAt`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.NodeRecQ7
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.SVWalk Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7 Nock.NockVMROM.Thm54.VclL.Compute.LogUp Nock.NockVMROM.Thm54.CoordinateCompiler

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Sel
variable {F K K' : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [DecidableEq F] [DecidableEq K]
  [Field K'] [Algebra F K'] [FiniteDimensional F K'] [DecidableEq K'] {hC : ℕ} {S : MemShape}
  {T : TableSpec} [WideTable T]

/-- **The decoded state of the gathered row is the raw one-hot state** (any gather, any wide table). -/
theorem rowLabel_fst_of_selAt (G : CoordGather F K') (V : VerifierData F K hC S)
    (chalV pubVal : ℕ → F) (Q : Fin T.width → F[X]) (r : Fin V.N) (st : State)
    (hst : SelAt (rawEnvQ7 V chalV pubVal Q r) st) :
    (rowLabel (envsVG G V chalV pubVal Q r)).1 = st := by
  rw [rowLabel_fst, ← stateOfBase_selAt _ st hst]
  congr 1; funext k
  split_ifs with hk
  · rw [envsVG_base (T := T) G V chalV pubVal Q r k hk]
    simp [rawEnvQ7, envOfTrace, show k < T.width by have := WideTable.hw (T := T); omega]
  · rfl

end Sel

/-! ## The 409-wide tower table (CF-T step 3a) -/

def tableVCLT (hC : ℕ) : TableSpec where
  width := vclWidthT
  colRound := fun j => if j.1 < 232 then colRoundVCLE j.1 else if j.1 < 388 then 1
    else if j.1 = z1Col then 1 else 2
  height := hC

instance tableVCLT_wide (hC : ℕ) : WideTable (tableVCLT hC) where
  hw := by simp [tableVCLT, vclWidthT]
  agree := fun c hc => by simp [tableVCLT, hc]
  le_two := fun j => by
    simp only [tableVCLT]
    split_ifs
    · exact colRoundVCLE_le_two ⟨j.1, by assumption⟩
    · norm_num
    · norm_num
    · norm_num

theorem tableVCLT_width (hC : ℕ) : (tableVCLT hC).width = 410 := rfl

section NodeRec
variable {F K : Type} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- **The serial of an accepted tower trace**: column `220` of row `r` is `r` (tower analogue of
`serial_eq_row`; serial gates from `TowerRowHolds.serial`, masks from `towerRowFactsQ7`). -/
theorem towerSerial_eq_row (V : VerifierData F K hC S) (chalV pubVal : ℕ → F)
    (hadj : V.AdjacentC)
    (P : Fin (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC) P)
    (hinj : Function.Injective V.computeNodes) (r : Fin V.N) :
    (rawEnvQ7 V chalV pubVal P r).trace serialCol = (r : F) := by
  have RF := towerRowFactsQ7 δ V.hN V.computeNodes V.basis chalV pubVal V.orbitC P hsat
    V.claim pubVal hinj
  have hs := ((computeChipVCLQ7T_sat_iff V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC P).1 hsat).2
  have hgate : ∀ i : Fin V.N, ∀ g ∈ (serialGates : List (CoeffExpr F)),
      g.eval (rawEnvQ7 V chalV pubVal P i) = 0 := fun i g hg =>
    ((vclGatesQ7T_iff δ V.basis V.N _ rfl _).mp
      (hs _ (by simp [rowNodeSet] : V.computeNodes i ∈ rowNodeSet V.computeNodes))).serial g hg
  have mask0 : ∀ i : Fin V.N, (rawEnvQ7 V chalV pubVal P i).trace 11 = if (i : ℕ) = 0 then 1 else 0 :=
    fun i => (RF.masks i).1
  have mask1 : ∀ i : Fin V.N, (rawEnvQ7 V chalV pubVal P i).trace 12 =
      if (i : ℕ) = V.N - 1 then 1 else 0 := fun i => (RF.masks i).2
  have hnext : ∀ (i : Fin V.N) (hi : (i : ℕ) + 1 < V.N),
      (rawEnvQ7 V chalV pubVal P i).traceNext serialCol =
        (rawEnvQ7 V chalV pubVal P ⟨(i : ℕ) + 1, hi⟩).trace serialCol := by
    intro i hi
    have ha := hadj i hi
    simp only [rawEnvQ7, envOfTrace]
    split_ifs
    · rw [ha]
    · rfl
  obtain ⟨r, hr⟩ := r
  induction r with
  | zero =>
      have := (serialInitGate_eval _).1 (hgate ⟨0, hr⟩ _ (by simp [serialGates]))
      rw [mask0] at this
      simpa using this
  | succ k ih =>
      have hk : k < V.N := by omega
      have hstep := (serialStepGate_eval _).1 (hgate ⟨k, hk⟩ _ (by simp [serialGates]))
      rw [mask1] at hstep
      have hne : ¬ (k = V.N - 1) := by omega
      simp only [hne, if_false] at hstep
      rcases hstep with h | h
      · exact absurd h zero_ne_one
      · rw [hnext ⟨k, hk⟩ hr] at h
        rw [h, ih hk]; push_cast; ring

/-- A `z1` identity gate at a row with `z1 = 1` and the selector on gives entry `3 + c` of
the path record equal to entry `c` (`𝕂′`). -/
theorem z1Eq_entry (b : Basis (Fin 3) F K) (env : Env F) (sel : ℕ) (r : Fin 8 → Entry) (c : Fin 3)
    (hg : ∀ g ∈ qGates b (z1EqQ F δ sel r c), g.eval env = 0)
    (hz : env.trace z1Col = 1) (hs : env.trace sel = 1) :
    Q.val δ (entryQ F (r ⟨3 + (c : ℕ), by omega⟩)) (gatherEnv b env) env =
      Q.val δ (entryQ F (r ⟨(c : ℕ), by omega⟩)) (gatherEnv b env) env := by
  have h := (Q.isZero_iff δ _ env _).mp ((qGates_iff b (isCoordEnv_gather b env) _).mp hg)
  rw [z1EqQ, qmul_val, qlift_val, qsub_val] at h
  simp only [CoeffExpr.eval, selVar, hz, hs, mul_one, map_one, one_mul] at h
  exact sub_eq_zero.mp h

/-- The path record's child equals its root at a `z1` row (OP0 / OP9 identities). -/
theorem z1_child_root (b : Basis (Fin 3) F K) (env : Env F) (sel : ℕ) (r : Fin 8 → Entry)
    (hg : ∀ c : Fin 3, ∀ g ∈ qGates b (z1EqQ F δ sel r c), g.eval env = 0)
    (hz : env.trace z1Col = 1) (hs : env.trace sel = 1) :
    RV.pathChild (recValQ δ (gatherEnv b env) env r) = RV.pathRoot (recValQ δ (gatherEnv b env) env r) := by
  have e := fun c => z1Eq_entry δ b env sel r c (hg c) hz hs
  simp only [RV.pathChild, RV.pathRoot, RV.fpAt]
  congr 1
  · exact e 0
  · exact e 1
  · exact e 2

/-- **At an accepted `s0` row the path slot is active or the row is an axis-1 `z1` row**
(child = root, decoded axis `1`). -/
theorem towerP_act_or_ident (b : Basis (Fin 3) F K) (n : ℕ)
    (env : Env F) (hg : ∀ g ∈ vclGatesQ7T n (MemoryTable.pwScaleExp K) b δ, g.eval env = 0) :
    (SelAt env .s0 → actPQ (K := K) δ env 0 = 1 ∨
      (RV.pathChild (recPQ δ (gatherEnv b env) env 0) = RV.pathRoot (recPQ δ (gatherEnv b env) env 0) ∧
        RecordCarrier.natLift (algebraMap F K (env.trace axCol)) = 1)) ∧
    (SelAt env .s9 → actPQ (K := K) δ env 1 = 1 ∨
      (RV.pathChild (recPQ δ (gatherEnv b env) env 1) = RV.pathRoot (recPQ δ (gatherEnv b env) env 1) ∧
        RecordCarrier.natLift (algebraMap F K (env.trace axCol)) = 1)) := by
  have hT := ((vclGatesQ7T_iff δ b n _ rfl env).mp hg).z1
  have hbool := z1_bool_of_gates δ b env hT
  have hax : env.trace z1Col = 1 → RecordCarrier.natLift (algebraMap F K (env.trace axCol)) = 1 := by
    intro hz
    have h1 := hT z1AxGate (by simp [z1Gates])
    simp only [z1AxGate, CoeffExpr.eval, hz, one_mul] at h1
    rw [sub_eq_zero.mp h1, map_one, ← Nat.cast_one]
    exact RecordCarrier.natLift_natCast (CharP.char_is_prime K (ringChar K)).one_lt
  have hq : ∀ (sel : ℕ) (r : Fin 8 → Entry),
      (∀ g ∈ (List.finRange 3).flatMap (fun c => qGates b (z1EqQ F δ sel r c)), g.eval env = 0) →
      ∀ c : Fin 3, ∀ g ∈ qGates b (z1EqQ F δ sel r c), g.eval env = 0 :=
    fun sel r h c g hg => h g (List.mem_flatMap.mpr ⟨c, List.mem_finRange c, hg⟩)
  have h0 : ∀ g ∈ (List.finRange 3).flatMap (fun c => qGates b (z1EqQ F δ 0 op0PathRec c)), g.eval env = 0 :=
    fun g hg => hT g (by simp only [z1Gates, List.mem_append]; exact Or.inl (Or.inr hg))
  have h9 : ∀ g ∈ (List.finRange 3).flatMap (fun c => qGates b (z1EqQ F δ 9 op9PathRec c)), g.eval env = 0 :=
    fun g hg => hT g (by simp only [z1Gates, List.mem_append]; exact Or.inr hg)
  refine ⟨fun hsel => ?_, fun hsel => ?_⟩
  · have ht : env.trace 0 = 1 := by rw [selAt_trace hsel 0 (by norm_num)]; simp [selIdx]
    rcases hbool with hz | hz
    · left; simp only [actPQ, ht, hz, sub_zero, mul_one, map_one]
    · right; exact ⟨z1_child_root δ b env 0 op0PathRec (hq _ _ h0) hz ht, hax hz⟩
  · have ht : env.trace 9 = 1 := by rw [selAt_trace hsel 9 (by norm_num)]; simp [selIdx]
    rcases hbool with hz | hz
    · left; simp only [actPQ, ht, hz, sub_zero, mul_one, map_one]
    · right; exact ⟨z1_child_root δ b env 9 op9PathRec (hq _ _ h9) hz ht, hax hz⟩

/-- **`node_records` at the tower** from acceptance at the tower chip: gather `towerGather δ V.basis`,
reader `towerReader δ V.basis`, table `tableVCLT hC`.  Hypotheses: the chip is the tower chip of `V`'s
rows, acceptance of the trace `P`, injective nodes; `hz`/`hzi` the coin facts, `hadj` the node adjacency, `hNp`. -/
theorem towerNodeRecordsQ7 (V : VerifierData F K hC S) (chalV pubVal : ℕ → F)
    (P : Fin (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7T V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC) P)
    (hinj : Function.Injective V.computeNodes)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hcharQ : ∀ n : ℕ, n ≤ 11 → (n : Quad (algebraMap F K δ)) = 1 → n = 1)
    (hz : zQ (cdOfGG (towerGather δ V.basis) V chalV pubVal) chalV ≠ 0)
    (hzi : (towerGather δ V.basis).chalSlot chalV 5 =
      (zQ (cdOfGG (towerGather δ V.basis) V chalV pubVal) chalV)⁻¹)
    (hadj : V.AdjacentC)
    (hNp : V.N ≤ ringChar (Quad (algebraMap F K δ))) (bm : ∀ t, B0Cols F (S.table t))
    (u : NTree ((State × DTcomp (Quad (algebraMap F K δ))) × ℕ))
    (hu : InTree (treeVG (towerGather δ V.basis) V chalV pubVal P) u)
    (j : ℕ) (hj : j < recordCount u.label.1.1) :
    (∃ a : Fin 3, ∃ x ∈ reqRecsQ7G (towerReader δ V.basis) V chalV pubVal P a,
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).root a x =
        (traceRecOf u.label j).root ∧
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).child a x =
        (traceRecOf u.label j).child ∧
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).key a x =
        recKeyQ7' V (b0 (T := tableVCLT hC) P) u.label.1.1 u.label.2 j ∧
      (RV.recordViewVCL F K (Quad (algebraMap F K δ)) (tableVCLT hC) S hC).axis a V
          (b0 (T := tableVCLT hC) P) bm x =
        joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLT hC) P)) u.label.2 j) ∨
    (((u.label.1.1 = .s0 ∧ j = 1) ∨ (u.label.1.1 = .s9 ∧ j = 2)) ∧
      joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLT hC) P)) u.label.2 j = 1 ∧
      (traceRecOf u.label j).child = (traceRecOf u.label j).root) := by
  have RF := towerRowFactsQ7 δ V.hN V.computeNodes V.basis chalV pubVal V.orbitC P hsat
    V.claim pubVal hinj
  have hrow : ∀ r : Fin V.N, ∃ st, SelAt (rawEnvQ7 V chalV pubVal P r) st ∧
      (rowLabel (envsVG (towerGather δ V.basis) V chalV pubVal P r)).1 = st := fun r => by
    have hg := ((computeChipVCLQ7T_sat_iff V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC P).1 hsat).2
      _ (by simp [rowNodeSet] : V.computeNodes r ∈ rowNodeSet V.computeNodes)
    obtain ⟨st, hst⟩ := selAt_of_towerRow δ V.basis V.N _ hg hchar
    exact ⟨st, hst, rowLabel_fst_of_selAt (T := tableVCLT hC) _ V chalV pubVal P r st hst⟩
  have hgr : ∀ r : Fin V.N, ∀ g ∈ vclGatesQ7T V.N (MemoryTable.pwScaleExp K) V.basis δ,
      g.eval (rawEnvQ7 V chalV pubVal P r) = 0 := fun r =>
    ((computeChipVCLQ7T_sat_iff V.hN V.computeNodes V.basis δ chalV pubVal V.orbitC P).1 hsat).2
      _ (by simp [rowNodeSet] : V.computeNodes r ∈ rowNodeSet V.computeNodes)
  have := node_records_Q7G (T := tableVCLT hC) (G := towerGather δ V.basis) (towerReader δ V.basis) V chalV pubVal P RF hcharQ hz hzi
    hrow (towerSerial_eq_row δ V chalV pubVal hadj P hsat hinj)
    (fun r => (towerP_act_or_ident δ V.basis V.N _ (hgr r)).1)
    (fun r => (towerP_act_or_ident δ V.basis V.N _ (hgr r)).2) hNp bm u hu j hj
  exact this

end NodeRec

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
