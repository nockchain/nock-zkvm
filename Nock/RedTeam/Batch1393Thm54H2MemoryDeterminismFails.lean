/-
  Nock/RedTeam/Batch1393Thm54H2MemoryDeterminismFails.lean

**It fails on every `verify_child` row.**  `DeployedStaging.memoryColRound` stages roles `3, 4,
  8, 9, 13, 14` in round `2`.  On a `verify_child` row the deployed gates bind them only through
  * the class gates `q = 3, 4` (`pt.pw = lc.pw + λ^{n−1}·ts`, `pt.counts = lc.counts + λ^{n−1}·ts`,
    `class3_vc_eval` / `class4_vc_eval`) — DIFFERENCES `pt − lc`, and
  * the walk, through `RLC^γ(x^mem) ∋ γ⁴·counts + γ⁵·pw` of the row's own label and of its child
    payload — the RLC at the sampled `γ` (memory slot `7`).
  The bottom pins (`q = 8, 9, 13, 14`) pin nothing on a `verify_child` row but `rc`.  So the shift `pw, lc.pw ↦ + a`, `counts, lc.counts ↦ − γ·a`
  is invisible to every gate.

  **`vc_shift_accepted`**: for EVERY tuple `c`, EVERY trace `Qm` accepted at `memoryChipAt c`,
  every non-first, non-last, non-root `verify_child` row `i` and every `a : 𝕂`, the trace
  `pertQm … i a` (Lagrange bumps on the twelve physical columns `15..20`, `30..35` at row `i`) is
  ALSO accepted at `memoryChipAt c`. `determinism_fails`: two accepted traces at the same `c`,
  equal polynomial for polynomial on every round-`0`/`1` column, with different role `3` (`pt.pw`)
  at row `i` (for `a ≠ 0`). So `pw`/`counts` and the child cells `8, 9` are NOT functions of the
  round-`≤1` columns and `λ` on accepted traces, at any coin.

  Recorded beside it (`class3_vc_eval`, the accepted-trace identity): on every accepted
  `verify_child` row `pt.pw − lc.pw = λ^{n−1}·ts` with `ts` (role `26`) round `2` and honestly
  `α^e` — the memory timestamp coin enters the label (`MIN-SCHEDULE` C2).

  -- the paper
-/
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
import Nock.RedTeam.Batch1392Thm54H2MemoryCellReadInstrument
import Mathlib.LinearAlgebra.Lagrange

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1393

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.MemoryTable
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.RedTeam.Batch1392

/-! ## A. The class gates `q = 3, 4` at a `verify_child` row -/

section Class

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]

theorem memQuantity_vc_3 :
    MemoryFactorizationScope.memQuantity (K := K) .verify_child 3 =
      .Sub (Reified.tc 7) (.Add (Reified.tc 12)
        (.Mul (MemoryFactorizationScope.lamScaleE (K := K)) (Reified.tc 30))) := rfl

theorem memQuantity_vc_4 :
    MemoryFactorizationScope.memQuantity (K := K) .verify_child 4 =
      .Sub (Reified.tc 8) (.Add (Reified.tc 13)
        (.Mul (MemoryFactorizationScope.lamScaleE (K := K)) (Reified.tc 30))) := rfl

/-- **The accepted-trace identity, `pt.pw`:** `pt.pw − (lc.pw + λ^{n−1}·ts)`. -/
theorem class3_vc_eval (eK : Env K) (eF : Env F)
    (hone : MemoryPaperFactorization.BaseOneHot eF .verify_child) :
    (paperClassGate (K := K) (F := F) 3).eval eK eF =
      eK.trace 3 - (eK.trace 8 + eK.chal 8 ^ MemoryTable.pwScaleExp K * eK.trace 26) := by
  rw [paperClassGate, selScale_eval eK eF .verify_child hone, memQuantity_vc_3]
  simp [Expr.subst, memorySubst, Reified.tc, extVar, Expr.eval,
    MemoryFactorizationScope.lamScaleE, MemoryFactorizationScope.lamE]

/-- **The accepted-trace identity, `pt.counts`:** `pt.counts − (lc.counts + λ^{n−1}·ts)`. -/
theorem class4_vc_eval (eK : Env K) (eF : Env F)
    (hone : MemoryPaperFactorization.BaseOneHot eF .verify_child) :
    (paperClassGate (K := K) (F := F) 4).eval eK eF =
      eK.trace 4 - (eK.trace 9 + eK.chal 8 ^ MemoryTable.pwScaleExp K * eK.trace 26) := by
  rw [paperClassGate, selScale_eval eK eF .verify_child hone, memQuantity_vc_4]
  simp [Expr.subst, memorySubst, Reified.tc, extVar, Expr.eval,
    MemoryFactorizationScope.lamScaleE, MemoryFactorizationScope.lamE]

end Class

/-! ## B. The walk accumulation step at a `verify_child` successor: an RLC-invariant -/

section Walk

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- `specM knownNextVC walkAccStepInGate`, printed by the instrument (at `ZMod 5`) and checked by
`rfl` at the generic carrier (`walkAccNextVC_eq`).  The successor's roles `3, 4` enter only as
`γ⁴·K'4 + γ⁵·K'3` (its label) and roles `8, 9` only as `γ⁴·K'9 + γ⁵·K'8` (its child payload). -/
def walkAccNextVC : MS F :=
  (.add (.scale (.col .traceCur 154) (.mul (.var .traceNext 31) (.add (.mul (.pow (.var .challenge 7) 0) (.cnst 3)) (.add (.mul (.pow (.var .challenge 7) 1) (.var .traceNext 0)) (.add (.mul (.pow (.var .challenge 7) 2) (.var .traceNext 1)) (.add (.mul (.pow (.var .challenge 7) 3) (.var .traceNext 2)) (.add (.mul (.pow (.var .challenge 7) 4) (.var .traceNext 4)) (.mul (.pow (.var .challenge 7) 5) (.var .traceNext 3))))))))) (.scale (.sub (.opq 1) (.col .traceCur 5)) (.sub (.sub (.var .traceNext 33) (.var .traceCur 33)) (.mul (.var .traceCur 32) (.mul (.pow (.var .challenge 3) 1) (.add (.mul (.pow (.var .challenge 7) 0) (.var .traceNext 45)) (.add (.mul (.pow (.var .challenge 7) 1) (.var .traceNext 5)) (.add (.mul (.pow (.var .challenge 7) 2) (.var .traceNext 6)) (.add (.mul (.pow (.var .challenge 7) 3) (.var .traceNext 7)) (.add (.mul (.pow (.var .challenge 7) 4) (.var .traceNext 9)) (.mul (.pow (.var .challenge 7) 5) (.var .traceNext 8))))))))))))

theorem walkAccNextVC_eq :
    specM knownNextVC (MemoryWalkLabel.walkAccStepInGate (F := F)) = walkAccNextVC := rfl

/-- The successor-row shift of the four roles. -/
def shiftNextM (eK : Env K) (a : K) : Env K :=
  { eK with traceNext := fun r =>
      if r = 3 ∨ r = 8 then eK.traceNext r + a
      else if r = 4 ∨ r = 9 then eK.traceNext r - eK.chal 7 * a else eK.traceNext r }

/-- The current-row shift of the four roles. -/
def shiftCurM (eK : Env K) (a : K) : Env K :=
  { eK with trace := fun r =>
      if r = 3 ∨ r = 8 then eK.trace r + a
      else if r = 4 ∨ r = 9 then eK.trace r - eK.chal 7 * a else eK.trace r }

set_option maxHeartbeats 4000000 in
theorem walkAccNextVC_shift (eK : Env K) (eF : Env F) (a : K) :
    evalMS (shiftNextM eK a) eF (walkAccNextVC (F := F)) = evalMS eK eF walkAccNextVC := by
  simp only [walkAccNextVC, evalMS, evalCS, shiftNextM]
  norm_num
  ring

end Walk


/-! ## C. The row-local perturbation of an accepted memory trace -/

noncomputable section Pert

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-- Every point a memory row environment evaluates a column at. -/
def evalSupportM : Finset F :=
  rowNodeSet P.optimized.memoryNodes ∪
    (rowNodeSet P.optimized.memoryNodes).image (fun x => P.optimized.orbit.ω * x)

/-- The `𝕂`-shift per role: `+a` on `pt.pw`, `lc.pw`; `−γ·a` on `pt.counts`, `lc.counts`. -/
def roleShiftM (a : K) (r : ℕ) : K :=
  if r = 3 ∨ r = 8 then a else if r = 4 ∨ r = 9 then -(gamma c.1 * a) else 0

/-- Its physical-column image (`6 + 3r + k ↦ coord k`). -/
def colShiftM (a : K) (col : ℕ) : F :=
  if 6 ≤ col ∧ col < 180 then
    coord P.optimized.basis (roleShiftM c a ((col - 6) / 3))
      ⟨(col - 6) % 3, Nat.mod_lt _ (by norm_num)⟩
  else 0

def bumpM (i : Fin P.optimized.family.problem.cfg.memRows) : F[X] :=
  Lagrange.basis (evalSupportM P) id (P.optimized.memoryNodes i)

/-- **The perturbed memory trace.** -/
def pertQm (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) (a : K) :
    Fin (P.memoryChipAt c).rap.w → F[X] :=
  fun col => Qm col + Polynomial.C (colShiftM P c a col) * bumpM P i

theorem nodeM_mem (j : Fin P.optimized.family.problem.cfg.memRows) :
    P.optimized.memoryNodes j ∈ evalSupportM P := by
  simp [evalSupportM, rowNodeSet]

theorem succM_mem (j : Fin P.optimized.family.problem.cfg.memRows) :
    P.optimized.orbit.ω * P.optimized.memoryNodes j ∈ evalSupportM P := by
  simp only [evalSupportM, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨_, by simp [rowNodeSet], rfl⟩

theorem bumpM_eval (i : Fin P.optimized.family.problem.cfg.memRows) {y : F}
    (hy : y ∈ evalSupportM P) :
    (bumpM P i).eval y = if y = P.optimized.memoryNodes i then 1 else 0 := by
  unfold bumpM
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (nodeM_mem P i)
  · exact Lagrange.eval_basis_of_ne (v := id) (Ne.symm h) hy

theorem colShiftM_role (a : K) (r : ℕ) (k : Fin 3) :
    colShiftM P c a (6 + 3 * r + k) = coord P.optimized.basis (roleShiftM c a r) k := by
  unfold colShiftM
  have h1 : (6 + 3 * r + (k : ℕ) - 6) / 3 = r := by omega
  have h2 : (6 + 3 * r + (k : ℕ) - 6) % 3 = k := by omega
  split_ifs with hc
  · simp only [h1]; congr 1; exact Fin.ext h2
  · have hr : r ≠ 3 ∧ r ≠ 8 ∧ r ≠ 4 ∧ r ≠ 9 := by omega
    simp [roleShiftM, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, coord]

theorem colShiftM_off (a : K) (col : ℕ) (h : col ∉ pertCols) : colShiftM P c a col = 0 := by
  unfold colShiftM
  split_ifs with hc
  · have hr : ¬ ((col - 6) / 3 = 3 ∨ (col - 6) / 3 = 8) ∧
        ¬ ((col - 6) / 3 = 4 ∨ (col - 6) / 3 = 9) := by
      simp only [pertCols, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      omega
    simp [roleShiftM, hr.1, hr.2, coord]
  · rfl

theorem roleShiftM_off (a : K) (r : ℕ) (h : r ∉ pertRoles) : roleShiftM c a r = 0 := by
  simp only [pertRoles, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [roleShiftM, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The source environment of a projected trace at a row node. -/
abbrev envS (Q : Fin 182 → F[X]) (x : F) : Env F :=
  envOfTrace Q P.optimized.orbit.ω x (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c)

theorem projAt_pert (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) (a : K) (j : Fin 182) :
    projAt P c (pertQm P c Qm i a) j =
      projAt P c Qm j + Polynomial.C (colShiftM P c a j) * bumpM P i := rfl

theorem pert_envS_trace (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.memRows) (a : K) (col : ℕ) :
    (envS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j)).trace col =
      (envS P c (projAt P c Qm) (P.optimized.memoryNodes j)).trace col +
        if j = i then colShiftM P c a col else 0 := by
  simp only [envS, envOfTrace]
  split_ifs with hw hji hji
  · subst hji
    rw [projAt_pert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      bumpM_eval P j (nodeM_mem P j), if_pos rfl, mul_one]
  · rw [projAt_pert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      bumpM_eval P i (nodeM_mem P j)]
    have : P.optimized.memoryNodes j ≠ P.optimized.memoryNodes i :=
      fun h => hji (P.optimized.memoryNodes_injective h)
    simp [this]
  · subst hji
    have : colShiftM P c a col = 0 := by unfold colShiftM; rw [if_neg (by omega)]
    simp [this]
  · simp

theorem pert_envS_traceNext (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.memRows) (a : K) (col : ℕ) :
    (envS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j)).traceNext col =
      (envS P c (projAt P c Qm) (P.optimized.memoryNodes j)).traceNext col +
        if P.optimized.orbit.ω * P.optimized.memoryNodes j = P.optimized.memoryNodes i then
          colShiftM P c a col else 0 := by
  simp only [envS, envOfTrace]
  split_ifs with hw hji hji
  · rw [projAt_pert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      bumpM_eval P i (succM_mem P j), if_pos hji, mul_one]
  · rw [projAt_pert, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      bumpM_eval P i (succM_mem P j), if_neg hji, mul_zero, add_zero]
  · have : colShiftM P c a col = 0 := by unfold colShiftM; rw [if_neg (by omega)]
    simp [this]
  · simp

/-- The gathered `𝕂` environment of a projected trace. -/
abbrev envKS (Q : Fin 182 → F[X]) (x : F) : Env K :=
  gatherEnv P.optimized.basis memoryCol0 (envS P c Q x)

theorem gatherM_trace (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.memRows) (a : K) (r : ℕ) :
    (envKS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j)).trace r =
      (envKS P c (projAt P c Qm) (P.optimized.memoryNodes j)).trace r +
        if j = i then roleShiftM c a r else 0 := by
  simp only [envKS, gatherEnv, memoryCol0, pert_envS_trace P c Qm i j a]
  split_ifs with hji
  · simp only [add_smul, Finset.sum_add_distrib]
    congr 1
    have := reconstruct_coord P.optimized.basis (roleShiftM c a r)
    simp only [reconstruct] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [colShiftM_role P c a r k]
  · simp

theorem gatherM_traceNext (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.memRows) (a : K) (r : ℕ) :
    (envKS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j)).traceNext r =
      (envKS P c (projAt P c Qm) (P.optimized.memoryNodes j)).traceNext r +
        if P.optimized.orbit.ω * P.optimized.memoryNodes j = P.optimized.memoryNodes i then
          roleShiftM c a r else 0 := by
  simp only [envKS, gatherEnv, memoryCol0, pert_envS_traceNext P c Qm i j a]
  split_ifs with hji
  · simp only [add_smul, Finset.sum_add_distrib]
    congr 1
    have := reconstruct_coord P.optimized.basis (roleShiftM c a r)
    simp only [reconstruct] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [colShiftM_role P c a r k]
  · simp

theorem gatherM_chal (Q : Fin 182 → F[X]) (x : F) (q : Fin 9) :
    (envKS P c Q x).chal q = memoryKOfTuple c q := by
  simp only [envKS, envS, gatherEnv, memoryCol0, envOfTrace]
  simp_rw [memoryChalValOfTuple_slot P.optimized.basis c q]
  change reconstruct P.optimized.basis (coord P.optimized.basis (memoryKOfTuple c q)) =
    memoryKOfTuple c q
  exact reconstruct_coord P.optimized.basis (memoryKOfTuple c q)

theorem gatherM_gamma (Q : Fin 182 → F[X]) (x : F) :
    (envKS P c Q x).chal 7 = gamma c.1 := by
  rw [gatherM_chal P c Q x ⟨7, by decide⟩]; rfl

/-! ### Transfer of the mixed gates -/

theorem envAt_cur_eq (eK eK' : Env K) (a : K) (hK : ∀ r, eK'.trace r = eK.trace r + roleShiftM c a r)
    (hKn : eK'.traceNext = eK.traceNext) (hKc : eK'.chal = eK.chal) (hKp : eK'.pub = eK.pub)
    (v : VarKind × ℕ) (hv : ¬ (v.1 = .traceCur ∧ v.2 ∈ pertRoles)) :
    envAtK eK v.1 v.2 = envAtK eK' v.1 v.2 := by
  obtain ⟨k, r⟩ := v
  cases k
  · simp only [envAtK]; rw [hK r, roleShiftM_off c a r (fun h => hv ⟨rfl, h⟩), add_zero]
  · simp only [envAtK, hKn]
  · simp only [envAtK, hKc]
  · simp only [envAtK, hKp]

theorem envAt_next_eq (eK eK' : Env K) (a : K)
    (hK : ∀ r, eK'.traceNext r = eK.traceNext r + roleShiftM c a r)
    (hKt : eK'.trace = eK.trace) (hKc : eK'.chal = eK.chal) (hKp : eK'.pub = eK.pub)
    (v : VarKind × ℕ) (hv : ¬ (v.1 = .traceNext ∧ v.2 ∈ pertRoles)) :
    envAtK eK v.1 v.2 = envAtK eK' v.1 v.2 := by
  obtain ⟨k, r⟩ := v
  cases k
  · simp only [envAtK, hKt]
  · simp only [envAtK]; rw [hK r, roleShiftM_off c a r (fun h => hv ⟨rfl, h⟩), add_zero]
  · simp only [envAtK, hKc]
  · simp only [envAtK, hKp]

theorem envAtF_eq (eF eF' : Env F) (kind : VarKind)
    (ht : ∀ col, (kind = .traceCur → col ∉ pertCols) → eF'.trace col = eF.trace col)
    (hn : ∀ col, (kind = .traceNext → col ∉ pertCols) → eF'.traceNext col = eF.traceNext col)
    (hc : eF'.chal = eF.chal) (hp : eF'.pub = eF.pub)
    (v : VarKind × ℕ) (hv : ¬ (v.1 = kind ∧ v.2 ∈ pertCols)) :
    envAtK eF v.1 v.2 = envAtK eF' v.1 v.2 := by
  obtain ⟨k, col⟩ := v
  cases k
  · simp only [envAtK]; exact (ht col (fun h => fun hm => hv ⟨h.symm, hm⟩)).symm
  · simp only [envAtK]; exact (hn col (fun h => fun hm => hv ⟨h.symm, hm⟩)).symm
  · simp only [envAtK, hc]
  · simp only [envAtK, hp]

theorem blind_unpack {kind : VarKind} {lk lb : List (VarKind × ℕ)}
    (h : blindL kind lk lb = true) :
    (∀ v ∈ lk, ¬ (v.1 = kind ∧ v.2 ∈ pertRoles)) ∧ (∀ v ∈ lb, ¬ (v.1 = kind ∧ v.2 ∈ pertCols)) := by
  simp only [blindL, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  refine ⟨fun v hv hh => ?_, fun v hv hh => ?_⟩
  · rcases h.1 v hv with h1 | h1
    · exact h1 hh.1
    · simp [hh.2] at h1
  · rcases h.2 v hv with h1 | h1
    · exact h1 hh.1
    · simp [hh.2] at h1

theorem gate_index {L : List (MixedExpr F)} {g : MixedExpr F} (hg : g ∈ L) :
    ∃ k, (g, k) ∈ L.zipIdx ∧ L[k]? = some g := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  refine ⟨k, ?_, List.getElem?_eq_getElem hk⟩
  rw [List.mk_mem_zipIdx_iff_getElem?]
  exact List.getElem?_eq_getElem hk

/-- **Current-row transfer** at a non-first, non-last, non-root `verify_child` row. -/
theorem mixed_cur_invariant (eK eK' : Env K) (eF eF' : Env F) (a : K)
    (_hγ : eK.chal 7 = gamma c.1)
    (hK : ∀ r, eK'.trace r = eK.trace r + roleShiftM c a r)
    (hKn : eK'.traceNext = eK.traceNext) (hKc : eK'.chal = eK.chal) (hKp : eK'.pub = eK.pub)
    (hF : ∀ col, col ∉ pertCols → eF'.trace col = eF.trace col)
    (hFn : eF'.traceNext = eF.traceNext) (hFc : eF'.chal = eF.chal) (hFp : eF'.pub = eF.pub)
    (hcar : Carries eF knownVC) (hcar' : Carries eF' knownVC)
    (hone : MemoryPaperFactorization.BaseOneHot eF .verify_child)
    (hone' : MemoryPaperFactorization.BaseOneHot eF' .verify_child) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval eK' eF' = g.eval eK eF := by
  intro g hg
  obtain ⟨k, hz, hk⟩ := gate_index hg
  by_cases k2 : k = 2
  · subst k2
    rw [gate2_is_class3] at hk
    cases hk
    rw [class3_vc_eval eK' eF' hone', class3_vc_eval eK eF hone, hK 3, hK 8, hK 26, hKc]
    simp only [roleShiftM]; norm_num; ring
  by_cases k3 : k = 3
  · subst k3
    rw [gate3_is_class4] at hk
    cases hk
    rw [class4_vc_eval eK' eF' hone', class4_vc_eval eK eF hone, hK 4, hK 9, hK 26, hKc]
    simp only [roleShiftM]; norm_num; ring
  have hb := List.all_eq_true.mp (vc_cur_blind P.optimized.basis) (g, k) hz
  simp only [k2, k3, beq_iff_eq, Bool.or_eq_true, false_or] at hb
  have hbl := blind_unpack (blindAt_of_fast _ _ _ hb)
  rw [← specM_eval eK' eF' knownVC hcar' g, ← specM_eval eK eF knownVC hcar g]
  symm
  refine evalMS_congr eK eK' eF eF' _ (fun v hv => envAt_cur_eq c eK eK' a hK hKn hKc hKp v
    (hbl.1 v hv)) (fun v hv => envAtF_eq eF eF' .traceCur ?_ ?_ hFc hFp v (hbl.2 v hv))
  · intro col h; exact hF col (h rfl)
  · intro col _; rw [hFn]

/-- **Successor-row transfer** when the successor row is `verify_child`. -/
theorem mixed_next_invariant (eK eK' : Env K) (eF eF' : Env F) (a : K)
    (hγ : eK.chal 7 = gamma c.1)
    (hK : ∀ r, eK'.traceNext r = eK.traceNext r + roleShiftM c a r)
    (hKt : eK'.trace = eK.trace) (hKc : eK'.chal = eK.chal) (hKp : eK'.pub = eK.pub)
    (hF : eF'.trace = eF.trace)
    (hFn : ∀ col, col ∉ pertCols → eF'.traceNext col = eF.traceNext col)
    (hFc : eF'.chal = eF.chal) (hFp : eF'.pub = eF.pub)
    (hcar : Carries eF knownNextVC) (hcar' : Carries eF' knownNextVC) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval eK' eF' = g.eval eK eF := by
  intro g hg
  obtain ⟨k, hz, hk⟩ := gate_index hg
  by_cases k32 : k = 32
  · subst k32
    rw [gate32_is_walkAccStep] at hk
    cases hk
    rw [← specM_eval eK' eF' knownNextVC hcar', ← specM_eval eK eF knownNextVC hcar,
      walkAccNextVC_eq]
    have hagree : evalMS eK' eF' (walkAccNextVC (F := F)) =
        evalMS (shiftNextM eK a) eF (walkAccNextVC (F := F)) := by
      refine evalMS_congr _ _ _ _ _ (fun v _ => ?_) (fun v hv => ?_)
      · obtain ⟨kd, r⟩ := v
        cases kd
        · simp only [envAtK, shiftNextM, hKt]
        · simp only [envAtK, shiftNextM, hK r, roleShiftM, hγ]
          split_ifs <;> ring
        · simp only [envAtK, shiftNextM, hKc]
        · simp only [envAtK, shiftNextM, hKp]
      · have : bReads (walkAccNextVC (F := F)) = [(.traceCur, 154), (.traceCur, 5)] := rfl
        rw [this] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> simp [envAtK, hF]
    rw [hagree, walkAccNextVC_shift]
  have hb := List.all_eq_true.mp (vc_next_blind P.optimized.basis) (g, k) hz
  simp only [k32, beq_iff_eq, Bool.or_eq_true, false_or] at hb
  have hbl := blind_unpack (blindAt_of_fast _ _ _ hb)
  rw [← specM_eval eK' eF' knownNextVC hcar' g, ← specM_eval eK eF knownNextVC hcar g]
  symm
  refine evalMS_congr eK eK' eF eF' _ (fun v hv => envAt_next_eq c eK eK' a hK hKt hKc hKp v
    (hbl.1 v hv)) (fun v hv => envAtF_eq eF eF' .traceNext ?_ ?_ hFc hFp v (hbl.2 v hv))
  · intro col _; rw [hF]
  · intro col h; exact hFn col (h rfl)

theorem coeffM_eval_congr (X : List ℕ) (envF envF' : Env F)
    (ht : ∀ col, col ∉ X → envF'.trace col = envF.trace col)
    (hn : ∀ col, col ∉ X → envF'.traceNext col = envF.traceNext col)
    (hc : envF'.chal = envF.chal) (hp : envF'.pub = envF.pub) :
    ∀ g : CoeffExpr F, (∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ X) →
      g.eval envF' = g.eval envF
  | .const _, _ => rfl
  | .var .traceCur i, h => by
      simp only [CoeffExpr.eval]; exact ht i (h i (by simp [DeployedStaging.coeffTraceCols]))
  | .var .traceNext i, h => by
      simp only [CoeffExpr.eval]; exact hn i (h i (by simp [DeployedStaging.coeffTraceCols]))
  | .var .challenge i, _ => by simp only [CoeffExpr.eval, hc]
  | .var .publicVal i, _ => by simp only [CoeffExpr.eval, hp]
  | .add a b, h => by
      simp only [CoeffExpr.eval]
      rw [coeffM_eval_congr X envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc'])),
        coeffM_eval_congr X envF envF' ht hn hc hp b
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .sub a b, h => by
      simp only [CoeffExpr.eval]
      rw [coeffM_eval_congr X envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc'])),
        coeffM_eval_congr X envF envF' ht hn hc hp b
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .mul a b, h => by
      simp only [CoeffExpr.eval]
      rw [coeffM_eval_congr X envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc'])),
        coeffM_eval_congr X envF envF' ht hn hc hp b
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .neg a, h => by
      simp only [CoeffExpr.eval]
      rw [coeffM_eval_congr X envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .pow a _, h => by
      simp only [CoeffExpr.eval]
      rw [coeffM_eval_congr X envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]

theorem env_eq_of {L : Type*} (e e' : Env L) (h1 : e'.trace = e.trace)
    (h2 : e'.traceNext = e.traceNext) (h3 : e'.chal = e.chal) (h4 : e'.pub = e.pub) :
    e' = e := by
  cases e; cases e'; simp_all

theorem base_avoid (b : Module.Basis (Fin 3) F K) :
    ∀ g ∈ baseTransitionGates (F := F) (K := K) b,
      ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ pertCols := by
  have h : (baseTransitionGates (F := F) (K := K) b).all
      (fun g => (DeployedStaging.coeffTraceCols g).all (fun col => !pertCols.contains col)) =
        true := rfl
  intro g hg col hcol hm
  have := List.all_eq_true.mp (List.all_eq_true.mp h g hg) col hcol
  simp [hm] at this

theorem succM_ne_self (i : Fin P.optimized.family.problem.cfg.memRows)
    (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows) :
    P.optimized.orbit.ω * P.optimized.memoryNodes i ≠ P.optimized.memoryNodes i := by
  intro h
  have hadj := P.optimized.memoryOrbitAligned i hilast
  rw [mul_comm, h] at hadj
  have := congrArg Fin.val (P.optimized.memoryNodes_injective hadj)
  simp at this

theorem knownVC_avoid {k : VarKind} {col : ℕ} {v : ℤ} (h : knownVC k col = some v) :
    col ∉ pertCols := by
  intro hm
  simp only [pertCols, List.mem_cons, List.not_mem_nil, or_false] at hm
  cases k <;> simp only [knownVC] at h <;> try simp at h
  split_ifs at h with h1 h2 <;> omega

theorem knownNextVC_avoid {k : VarKind} {col : ℕ} {v : ℤ} (h : knownNextVC k col = some v) :
    col ∉ pertCols := by
  intro hm
  simp only [pertCols, List.mem_cons, List.not_mem_nil, or_false] at hm
  cases k <;> simp only [knownNextVC] at h <;> try simp at h
  split_ifs at h with h1 h2 <;> omega

theorem knownNextVC_spec {k : VarKind} {col : ℕ} {v : ℤ} (h : knownNextVC k col = some v) :
    k = .traceNext ∧ col < 4 ∧ v = if col = 3 then 1 else 0 := by
  cases k <;> simp only [knownNextVC] at h <;> try simp at h
  split_ifs at h with h1 h2
  · cases h; refine ⟨rfl, by omega, ?_⟩; rw [if_neg (by omega)]
  · cases h; subst h2; exact ⟨rfl, by omega, rfl⟩

theorem vc_sel (e : Env F) (h : MemoryPaperFactorization.BaseOneHot e .verify_child) :
    ∀ col, col < 4 → e.trace col = if col = 3 then 1 else 0 := by
  intro col hcol
  have hd := h .decompose
  have hh := h .halt
  have hr := h .read_root
  have hv := h .verify_child
  simp only [mopCol] at hd hh hr hv
  interval_cases col
  · simpa using hd
  · simpa using hh
  · simpa using hr
  · simpa using hv

theorem carries_transfer (known : VarKind → ℕ → Option ℤ) (eF eF' : Env F)
    (havoid : ∀ k col v, known k col = some v → col ∉ pertCols)
    (ht : ∀ col, col ∉ pertCols → eF'.trace col = eF.trace col)
    (hn : ∀ col, col ∉ pertCols → eF'.traceNext col = eF.traceNext col)
    (hc : eF'.chal = eF.chal) (hp : eF'.pub = eF.pub)
    (h : Carries eF known) : Carries eF' known := by
  intro k col v hv
  have := h k col v hv
  cases k <;> simp only [envAtF] at this ⊢
  · rw [ht col (havoid _ _ _ hv)]; exact this
  · rw [hn col (havoid _ _ _ hv)]; exact this
  · rw [hc]; exact this
  · rw [hp]; exact this

/-! ### The accepted trace and its masks -/

section Accepted

variable (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
include hsat

theorem envS_eq_envF (i : Fin P.optimized.family.problem.cfg.memRows) :
    envS P c (projAt P c Qm) (P.optimized.memoryNodes i) = MemoryWalkDeployed.envF P c Qm i :=
  envF_eq_base P c Qm i

theorem projAt_rootMask :
    projAt P c Qm ⟨153, by norm_num⟩ =
      OptimizedMemoryCanonicalTrace.rootRowMask P.optimized.memoryNodes
        P.optimized.family.problem.cfg.kMem := by
  have hbind := (source_sat_at P c Qm hsat).2
  have hw : (MemoryWalkDeployed.sourceAt P c).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  have h153 : 153 < (MemoryWalkDeployed.sourceAt P c).rap.w := by rw [hw]; norm_num
  have h2 := hbind ⟨2, by change (2 : ℕ) < 4; norm_num⟩
  have hc2 : (MemoryWalkDeployed.sourceAt P c).preprocessingColumn
      ⟨2, by change (2 : ℕ) < 4; norm_num⟩ = ⟨153, h153⟩ := rfl
  rw [hc2] at h2
  change projAt P c Qm ⟨153, h153⟩ =
    (MemoryWalkDeployed.sourceAt P c).preprocessing ⟨2, by change (2 : ℕ) < 4; norm_num⟩ at h2
  simpa [MemoryWalkDeployed.sourceAt, namedSourceMemoryRAP] using h2

theorem envS_trace153 (i : Fin P.optimized.family.problem.cfg.memRows) :
    (envS P c (projAt P c Qm) (P.optimized.memoryNodes i)).trace 153 =
      (if (i : ℕ) < P.optimized.family.problem.cfg.kMem then 1 else 0) := by
  have h153 : (153 : ℕ) < 182 := by norm_num
  simp only [envS, envOfTrace, dif_pos h153]
  rw [projAt_rootMask P c Qm hsat,
    OptimizedMemoryCanonicalTrace.rootRowMask_eval _ _ P.optimized.memoryNodes_injective]

theorem carries_vc (i : Fin P.optimized.family.problem.cfg.memRows)
    (hi0 : (i : ℕ) ≠ 0) (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows)
    (hroot : P.optimized.family.problem.cfg.kMem ≤ (i : ℕ))
    (hvc : MemoryPaperFactorization.BaseOneHot
      (envS P c (projAt P c Qm) (P.optimized.memoryNodes i)) .verify_child) :
    Carries (envS P c (projAt P c Qm) (P.optimized.memoryNodes i)) knownVC := by
  intro k col v hv
  cases k
  rotate_left
  · simp [knownVC] at hv
  · simp [knownVC] at hv
  · simp [knownVC] at hv
  simp only [knownVC] at hv
  · have h4 := MemoryWalkDeployed.envF_trace4 P c Qm hsat i
    have h5 := MemoryWalkDeployed.envF_trace5 P c Qm hsat i
    rw [← envS_eq_envF P c Qm hsat i] at h4 h5
    have h153 := envS_trace153 P c Qm hsat i
    have hd := hvc .decompose
    have hh := hvc .halt
    have hr := hvc .read_root
    have hv' := hvc .verify_child
    simp only [mopCol] at hd hh hr hv'
    simp only [envAtF]
    split_ifs at hv with hA hB
    · cases hv
      rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using hd
      · simpa using hh
      · simpa using hr
      · rw [h4, if_neg hi0]; simp
      · rw [h5, if_neg (by simp only [MemoryWalkDeployed.memRows]; omega)]; simp
      · rw [h153, if_neg (by omega)]; simp
    · cases hv; subst hB; simpa using hv'

/-- **THE COUNTEREXAMPLE.**  The `verify_child` shift of an accepted memory trace is accepted, at
the same tuple. -/
theorem vc_shift_accepted (i : Fin P.optimized.family.problem.cfg.memRows)
    (hi0 : (i : ℕ) ≠ 0) (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows)
    (hroot : P.optimized.family.problem.cfg.kMem ≤ (i : ℕ))
    (hvc : MemoryPaperFactorization.BaseOneHot
      (envS P c (projAt P c Qm) (P.optimized.memoryNodes i)) .verify_child) (a : K) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (pertQm P c Qm i a) := by
  have hsrc := source_sat_at P c Qm hsat
  have hraw : (sourceMemoryRAP P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).Satisfies (projAt P c Qm) := hsrc.1
  rw [sourceMemoryRAP_satisfies_iff_language P.optimized.sampled] at hraw
  have hcar_i := carries_vc P c Qm hsat i hi0 hilast hroot hvc
  have hωi := succM_ne_self P i hilast
  have key : RAP.SatisfiesWithPreprocessing
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem)
      (projAt P c (pertQm P c Qm i a)) := by
    refine ⟨?_, ?_⟩
    · show (sourceMemoryRAP P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit
        (rowNodeSet P.optimized.memoryNodes)).Satisfies _
      rw [sourceMemoryRAP_satisfies_iff_language P.optimized.sampled]
      intro x hx
      have hj := hraw x hx
      simp only [rowNodeSet, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := hx
      rw [memorySourceTemplate_col0] at hj ⊢
      obtain ⟨hb, he, hx3, hm⟩ := hj
      -- the four base-env facts of row `j`
      have hT : ∀ col, col ∉ pertCols →
          (envS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j)).trace col =
            (envS P c (projAt P c Qm) (P.optimized.memoryNodes j)).trace col := by
        intro col hcol; rw [pert_envS_trace, colShiftM_off P c a col hcol]; simp
      have hN : ∀ col, col ∉ pertCols →
          (envS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j)).traceNext col =
            (envS P c (projAt P c Qm) (P.optimized.memoryNodes j)).traceNext col := by
        intro col hcol; rw [pert_envS_traceNext, colShiftM_off P c a col hcol]; simp
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro g hg
        rw [← hb g hg]
        refine coeffM_eval_congr pertCols _ _ hT hN rfl rfl g ?_
        exact base_avoid P.optimized.basis g hg
      · intro g hg; simp [equalityChecks] at hg
      · intro g hg
        simp [memorySourceTemplate, degreeOneEndpoints, degreeThreeEndpoints] at hg
      · intro g hg
        rw [← hm g hg]
        by_cases hji : j = i
        · subst hji
          refine mixed_cur_invariant P c
            (envKS P c (projAt P c Qm) (P.optimized.memoryNodes j))
            (envKS P c (projAt P c (pertQm P c Qm j a)) (P.optimized.memoryNodes j))
            (envS P c (projAt P c Qm) (P.optimized.memoryNodes j))
            (envS P c (projAt P c (pertQm P c Qm j a)) (P.optimized.memoryNodes j))
            a (gatherM_gamma P c _ _) ?_ ?_ rfl rfl ?_ ?_
            rfl rfl hcar_i ?_ hvc ?_ g hg
          · intro r; rw [gatherM_trace, if_pos rfl]
          · funext r; rw [gatherM_traceNext, if_neg hωi, add_zero]
          · exact hT
          · funext col; rw [pert_envS_traceNext, if_neg hωi, add_zero]
          · exact carries_transfer knownVC _ _ (fun _ _ _ h => knownVC_avoid h) hT hN rfl rfl hcar_i
          · intro st
            rw [hT _ (by cases st <;> decide)]
            exact hvc st
        · by_cases hω : P.optimized.orbit.ω * P.optimized.memoryNodes j =
              P.optimized.memoryNodes i
          · have hnextsel : ∀ col, col < 4 →
                (envS P c (projAt P c Qm) (P.optimized.memoryNodes j)).traceNext col =
                  (envS P c (projAt P c Qm) (P.optimized.memoryNodes i)).trace col := by
              intro col _; simp only [envS, envOfTrace, hω]
            have hcarN : Carries (envS P c (projAt P c Qm) (P.optimized.memoryNodes j))
                knownNextVC := by
              intro k col v hv
              obtain ⟨rfl, hlt, rfl⟩ := knownNextVC_spec hv
              simp only [envAtF]
              rw [hnextsel col hlt, vc_sel _ hvc col hlt]
              split_ifs <;> simp
            refine mixed_next_invariant P c
              (envKS P c (projAt P c Qm) (P.optimized.memoryNodes j))
              (envKS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j))
              (envS P c (projAt P c Qm) (P.optimized.memoryNodes j))
              (envS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j))
              a (gatherM_gamma P c _ _) ?_ ?_ rfl rfl ?_
              hN rfl rfl hcarN ?_ g hg
            · intro r; rw [gatherM_traceNext, if_pos hω]
            · funext r; rw [gatherM_trace, if_neg hji, add_zero]
            · funext col; rw [pert_envS_trace, if_neg hji, add_zero]
            · exact carries_transfer knownNextVC _ _ (fun _ _ _ h => knownNextVC_avoid h)
                (fun col _ => by rw [pert_envS_trace, if_neg hji, add_zero]) hN rfl rfl hcarN
          · have hE : envS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes j) =
                envS P c (projAt P c Qm) (P.optimized.memoryNodes j) := by
              refine env_eq_of _ _ ?_ ?_ rfl rfl
              · funext col; rw [pert_envS_trace, if_neg hji, add_zero]
              · funext col; rw [pert_envS_traceNext, if_neg hω, add_zero]
            exact congrArg (fun e => g.eval (gatherEnv P.optimized.basis memoryCol0 e) e) hE
    · intro jj
      have hj := hsrc.2 jj
      have hcol : ((namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
          P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
          (P.familyMemoryPublic c) P.optimized.orbit
          P.optimized.family.problem.cfg.kMem).preprocessingColumn jj : ℕ) ∉ pertCols := by
        fin_cases jj
        · change (4 : ℕ) ∉ pertCols; decide
        · change (5 : ℕ) ∉ pertCols; decide
        · change (153 : ℕ) ∉ pertCols; decide
        · change (154 : ℕ) ∉ pertCols; decide
      show projAt P c (pertQm P c Qm i a) _ = _
      erw [projAt_pert, colShiftM_off P c a _ hcol]
      simpa using hj
  exact (final_satisfies_iff_source P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem
    (pertQm P c Qm i a)).2 key

end Accepted

/-! ### What the perturbation did -/

theorem pertQm_off (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) (a : K)
    (col : Fin (P.memoryChipAt c).rap.w) (hcol : (col : ℕ) ∉ pertCols) :
    pertQm P c Qm i a col = Qm col := by
  simp [pertQm, colShiftM_off P c a col hcol]

theorem pertCols_round (col : ℕ) (h : col ∈ pertCols) : DeployedStaging.memoryColRound col = 2 := by
  simp only [pertCols, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pertM_role3 (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) (a : K) :
    (envKS P c (projAt P c (pertQm P c Qm i a)) (P.optimized.memoryNodes i)).trace 3 =
      (envKS P c (projAt P c Qm) (P.optimized.memoryNodes i)).trace 3 + a := by
  rw [gatherM_trace, if_pos rfl]; simp [roleShiftM]

/-- **Determinism fails.**  At every tuple, from any accepted trace with a non-first, non-last,
non-root `verify_child` row, there are two accepted traces that agree, polynomial for polynomial,
on every round-`0`/`1` column and differ in `pt.pw` (role `3`) of that row. -/
theorem determinism_fails (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hi0 : (i : ℕ) ≠ 0) (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.memRows)
    (hroot : P.optimized.family.problem.cfg.kMem ≤ (i : ℕ))
    (hvc : MemoryPaperFactorization.BaseOneHot
      (envS P c (projAt P c Qm) (P.optimized.memoryNodes i)) .verify_child) :
    ∃ Qm' : Fin (P.memoryChipAt c).rap.w → F[X],
      RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm' ∧
      (∀ col : Fin (P.memoryChipAt c).rap.w,
        DeployedStaging.memoryColRound (col : ℕ) ≤ 1 → Qm' col = Qm col) ∧
      (envKS P c (projAt P c Qm') (P.optimized.memoryNodes i)).trace 3 ≠
        (envKS P c (projAt P c Qm) (P.optimized.memoryNodes i)).trace 3 := by
  refine ⟨pertQm P c Qm i 1, vc_shift_accepted P c Qm hsat i hi0 hilast hroot hvc 1,
    fun col h => pertQm_off P c Qm i 1 col (fun hm => by rw [pertCols_round _ hm] at h; omega), ?_⟩
  rw [pertM_role3]
  simp

end Pert

end Nock.RedTeam.Batch1393

#print axioms Nock.RedTeam.Batch1393.vc_shift_accepted
#print axioms Nock.RedTeam.Batch1393.determinism_fails
#print axioms Nock.RedTeam.Batch1393.class3_vc_eval
#print axioms Nock.RedTeam.Batch1393.class4_vc_eval
#print axioms Nock.RedTeam.Batch1393.walkAccNextVC_shift
