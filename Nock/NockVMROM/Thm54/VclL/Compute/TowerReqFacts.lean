import Nock.NockVMROM.Thm54.VclL.Compute.TowerRecs
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S

/-!
# Route (d), CF-T step 3a : `reqFacts` of the tower chip at `Kio := Quad δ`

.

`exportReqFactsQ7T` / `pathReqFactsQ7T` are the `exportReqFactsQ7S` / `pathReqFactsQ7S` analogues:
from an accepted family of tower rows (`AcceptedRowsQ7T`: every row satisfies `vclGatesQ7T`, the
shift / first / last masks, constant challenges / publics), the active export (11 wide) and path
(8 wide) records have reciprocal `𝕂′` compressed denominators summing to the `𝕂′` terminal
`Quad.mk (Re pub) (Im pub)`.  The IO coins are a parameter `coins'` with `hcoins` (each row's
`coinsQ` is `coins'`, `coinsQ_chalVQ7T` at the frame).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Module Polynomial
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.Unhosted309 Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead

set_option autoImplicit false
set_option maxRecDepth 300000
set_option linter.unusedSectionVars false

noncomputable section

section Rows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

theorem algF_mul_mk (a : F) (x y : K) :
    algebraMap F (Quad (algebraMap F K δ)) a * Quad.mk _ x y = Quad.mk _ (a • x) (a • y) := by
  have h : algebraMap F (Quad (algebraMap F K δ)) a =
      algebraMap K (Quad (algebraMap F K δ)) (algebraMap F K a) := IsScalarTower.algebraMap_apply F K _ a
  rw [h, Quad.mk_smul, Algebra.smul_def, Algebra.smul_def]

theorem actXQ_bool (env : Env F) (st : State) (h : SelAt env st) (s : ℕ) :
    actXQ (K := K) δ env s = 0 ∨ actXQ (K := K) δ env s = 1 := by
  have ht := selAt_trace h
  rcases s with _ | _ | _ | s
  · right; rfl
  · simp only [actXQ, selSum_eval, slot1ExportSels, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [ht 2 (by norm_num), ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num),
      ht 8 (by norm_num), ht 9 (by norm_num)]
    cases st <;> simp [selIdx]
  · simp only [actXQ]; rw [ht 6 (by norm_num)]; cases st <;> simp [selIdx]
  · left; rfl

theorem actPQ_bool (env : Env F) (st : State) (h : SelAt env st)
    (hz : env.trace z1Col = 0 ∨ env.trace z1Col = 1) (s : ℕ) :
    actPQ (K := K) δ env s = 0 ∨ actPQ (K := K) δ env s = 1 := by
  have ht := selAt_trace h
  rcases s with _ | _ | s
  · simp only [actPQ]; rw [ht 0 (by norm_num)]
    rcases hz with hz | hz <;> rw [hz] <;> cases st <;> simp [selIdx]
  · simp only [actPQ]; rw [ht 9 (by norm_num)]
    rcases hz with hz | hz <;> rw [hz] <;> cases st <;> simp [selIdx]
  · left; rfl

/-- **`z1` is boolean** at a row satisfying the `z1` gates (`z1·(z1 − 1) = 0`). -/
theorem z1_bool_of_gates (b : Basis (Fin 3) F K) (env : Env F) (h : ∀ g ∈ z1Gates b δ, g.eval env = 0) :
    env.trace z1Col = 0 ∨ env.trace z1Col = 1 := by
  have h0 := h z1BoolGate (by simp [z1Gates])
  simp only [z1BoolGate, CoeffExpr.eval] at h0
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h0)

/-- The per-row export term of `accGatesT` is `Σ_s act_s · inv′_s`. -/
theorem termQ_export (env : Env F) :
    termQ δ b accSlotsX accSlotsXIm env =
      ∑ s ∈ Finset.range 3, actXQ δ env s * invXQ δ (gatherEnv b env) env s := by
  unfold termQ termVal
  simp only [accSlotsX, accSlotsXIm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, actXQ, invXQ, val_invQ, algF_mul_mk,
    Quad.mk_add, one_mul, CoeffExpr.eval, selVar, add_zero, one_smul, map_one, add_assoc]

theorem termQ_path (env : Env F) :
    termQ δ b accSlotsPT accSlotsPImT env =
      ∑ s ∈ Finset.range 2, actPQ δ env s * invPQ δ (gatherEnv b env) env s := by
  unfold termQ termVal
  simp only [accSlotsPT, accSlotsPImT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, actPQ, invPQ, val_invQ, algF_mul_mk,
    Quad.mk_add, one_mul, CoeffExpr.eval, selVar, add_zero, one_smul, map_one, add_assoc,
    actP0, actP9, notZ1]

end Rows

section Facts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))] (b : Basis (Fin 3) F K)

/-- **The one-hot state in `𝔽` from the tower row** (base gates, hence the selectors). -/
theorem selAt_of_towerRow [Fintype K] [CharP K (ringChar K)] (n : ℕ)
    (env : Env F) (hg : ∀ g ∈ vclGatesQ7T n (MemoryTable.pwScaleExp K) b δ, g.eval env = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) : ∃ st, SelAt env st := by
  have hbase := ((vclGatesQ7T_iff δ b n _ rfl env).mp hg).kept.base
  obtain ⟨st, hone⟩ := oneHot_of_base15 n b _ hbase hchar
  refine ⟨st, fun i hi => ?_⟩
  obtain ⟨t, rfl⟩ := exists_selIdx i hi
  have h1 := hone t
  rw [selIdx_opCol, source_trace_base _ _ (by cases t <;> decide)] at h1
  have h2 : (pullEnv env).trace (selIdx t) = env.trace (selIdx t) :=
    pullEnv_trace_lt _ _ (by cases t <;> decide)
  change algebraMap F K ((pullEnv env).trace (selIdx t)) = _ at h1
  rw [h2] at h1
  have hF : env.trace (selIdx t) = if t = st then 1 else 0 := by
    by_cases ht : t = st
    · rw [if_pos ht] at h1 ⊢
      exact (algebraMap F K).injective (by rw [h1, map_one])
    · rw [if_neg ht] at h1 ⊢
      exact (algebraMap F K).injective (by rw [h1, map_zero])
  cases st <;> cases t <;> simpa [selIdx] using hF

/-- An accepted family of tower rows. -/
structure AcceptedRowsQ7T (n N : ℕ) (envs : ℕ → Env F) (chalV pubVal : ℕ → F) : Prop where
  hN : 0 < N
  gates : ∀ i < N, ∀ g ∈ vclGatesQ7T n (MemoryTable.pwScaleExp K) b δ, g.eval (envs i) = 0
  shift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j
  first : (envs 0).trace 11 = 1
  notLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0
  last : (envs (N - 1)).trace 12 = 1
  chal : ∀ i, (envs i).chal = chalV
  pub : ∀ i, (envs i).pub = pubVal

variable {δ b}
variable [Fintype K] [CharP K (ringChar K)]

/-- **The tower export accumulator's `reqFacts`** at `Kio := Quad δ`. -/
def exportReqFactsQ7T (n N : ℕ) (envs : ℕ → Env F)
    (chalV pubVal : ℕ → F) (A : AcceptedRowsQ7T δ b n N envs chalV pubVal)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (coins' : FiniteIO.IOCoins (Quad (algebraMap F K δ)))
    (hcoins : ∀ i < N, coinsQ δ (gatherEnv b (envs i)) (envs i) = coins') :
    ReqIOFacts (FiniteIO.compress (m := 11) coins')
      (Quad.mk _ (limbVal b pubVal rhoExportPub) (limbVal b pubVal rhoExportImPub)) := by
  classical
  let act : ℕ → ℕ → Quad (algebraMap F K δ) := fun i s => if i < N then actXQ δ (envs i) s else 0
  let inv : ℕ → ℕ → Quad (algebraMap F K δ) := fun i s =>
    if act i s = 1 then invXQ δ (gatherEnv b (envs i)) (envs i) s else 0
  have hsel : ∀ i < N, ∃ st, SelAt (envs i) st := fun i hi =>
    selAt_of_towerRow δ b n _ (A.gates i hi) hchar
  have hbool : ∀ i s, act i s = 0 ∨ act i s = 1 := by
    intro i s
    by_cases hi : i < N
    · obtain ⟨st, hst⟩ := hsel i hi
      simp only [act, hi, if_true]; exact actXQ_bool δ _ st hst s
    · left; simp [act, hi]
  have hinv : ∀ i s, s < 3 → inv i s * FiniteIO.compress coins'
      (recXQ δ (gatherEnv b (envs i)) (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := hsel i hi
      have ha' : actXQ (K := K) δ (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      have hT := (vclGatesQ7T_iff δ b n _ rfl (envs i)).mp (A.gates i hi)
      rw [← hcoins i hi]
      exact export_invQ7T _ _ st hst hT.slot0 hT.slot1 hT.slot2 s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 3, act i s * inv i s =
      Quad.mk _ (limbVal b pubVal rhoExportPub) (limbVal b pubVal rhoExportImPub) := by
    have hrows := accGatesT_export_rows δ b N A.hN envs
      (fun i hi g hm => ((vclGatesQ7T_iff δ b n _ rfl (envs i)).mp (A.gates i hi)).acc g hm)
      A.shift A.first A.notLast A.last
    rw [A.pub] at hrows
    rw [← hrows]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    rw [termQ_export]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hbool i s with h0 | h1
    · have : actXQ (K := K) δ (envs i) s = 0 := by simpa [act, hi'] using h0
      rw [h0, this]; ring
    · have : actXQ (K := K) δ (envs i) s = 1 := by simpa [act, hi'] using h1
      simp [inv, h1, this]
  exact reqIOFacts_of_rows N 3 act inv (fun i s => recXQ δ (gatherEnv b (envs i)) (envs i) s)
    (FiniteIO.compress coins') _ hbool
    (fun i s => by
      by_cases hs : s < 3
      · exact hinv i s hs
      · have h0 : act i s = 0 := by
          rcases s with _ | _ | _ | s
          · omega
          · omega
          · omega
          · by_cases hi : i < N <;> simp [act, hi, actXQ]
        simp [inv, h0])
    hsum

/-- **The tower path accumulator's `reqFacts`** at `Kio := Quad δ`. -/
def pathReqFactsQ7T (n N : ℕ) (envs : ℕ → Env F)
    (chalV pubVal : ℕ → F) (A : AcceptedRowsQ7T δ b n N envs chalV pubVal)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (coins' : FiniteIO.IOCoins (Quad (algebraMap F K δ)))
    (hcoins : ∀ i < N, coinsQ δ (gatherEnv b (envs i)) (envs i) = coins') :
    ReqIOFacts (FiniteIO.compress (m := 8) coins')
      (Quad.mk _ (limbVal b pubVal rhoPathPub) (limbVal b pubVal rhoPathImPub)) := by
  classical
  let act : ℕ → ℕ → Quad (algebraMap F K δ) := fun i s => if i < N then actPQ δ (envs i) s else 0
  let inv : ℕ → ℕ → Quad (algebraMap F K δ) := fun i s =>
    if act i s = 1 then invPQ δ (gatherEnv b (envs i)) (envs i) s else 0
  have hsel : ∀ i < N, ∃ st, SelAt (envs i) st := fun i hi =>
    selAt_of_towerRow δ b n _ (A.gates i hi) hchar
  have hbool : ∀ i s, act i s = 0 ∨ act i s = 1 := by
    intro i s
    by_cases hi : i < N
    · obtain ⟨st, hst⟩ := hsel i hi
      simp only [act, hi, if_true]
      exact actPQ_bool δ _ st hst
        (z1_bool_of_gates δ b _ ((vclGatesQ7T_iff δ b n _ rfl (envs i)).mp (A.gates i hi)).z1) s
    · left; simp [act, hi]
  have hinv : ∀ i s, s < 2 → inv i s * FiniteIO.compress coins'
      (recPQ δ (gatherEnv b (envs i)) (envs i) s) = act i s := by
    intro i s hs
    by_cases ha : act i s = 1
    · have hi : i < N := by by_contra hi; simp [act, hi] at ha
      obtain ⟨st, hst⟩ := hsel i hi
      have ha' : actPQ (K := K) δ (envs i) s = 1 := by simpa [act, hi] using ha
      simp only [inv, ha, if_true]
      have hT := (vclGatesQ7T_iff δ b n _ rfl (envs i)).mp (A.gates i hi)
      rw [← hcoins i hi]
      exact path_invQ7T _ _ st hst hT.slot1 hT.slot2 s hs ha'
    · rcases hbool i s with h0 | h1
      · simp [inv, h0]
      · exact absurd h1 ha
  have hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range 2, act i s * inv i s =
      Quad.mk _ (limbVal b pubVal rhoPathPub) (limbVal b pubVal rhoPathImPub) := by
    have hrows := accGatesT_path_rows δ b N A.hN envs
      (fun i hi g hm => ((vclGatesQ7T_iff δ b n _ rfl (envs i)).mp (A.gates i hi)).acc g hm)
      A.shift A.first A.notLast A.last
    rw [A.pub] at hrows
    rw [← hrows]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    rw [termQ_path]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases hbool i s with h0 | h1
    · have : actPQ (K := K) δ (envs i) s = 0 := by simpa [act, hi'] using h0
      rw [h0, this]; ring
    · have : actPQ (K := K) δ (envs i) s = 1 := by simpa [act, hi'] using h1
      simp [inv, h1, this]
  exact reqIOFacts_of_rows N 2 act inv (fun i s => recPQ δ (gatherEnv b (envs i)) (envs i) s)
    (FiniteIO.compress coins') _ hbool
    (fun i s => by
      by_cases hs : s < 2
      · exact hinv i s hs
      · have h0 : act i s = 0 := by
          rcases s with _ | _ | s
          · omega
          · omega
          · by_cases hi : i < N <;> simp [act, hi, actPQ]
        simp [inv, h0])
    hsum

end Facts

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
