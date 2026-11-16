import Nock.NockVMROM.Thm54.VclL.Compute.TowerKept
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.ComputePaperPacking

/-!
# The row-local kept gates of the tower compute chip, A-free

* `RowMatch env inp st pub dec ex`: the restated hypotheses (1)-(3) of DESIGN §(a) on an ARBITRARY
  source-layout environment: (1) the env read through `computeSubst` is `computeEnvFull inp (opSel st)
  pub dec ex` on trace `j < 94` and challenges `j < 5`, (2) the `computeAIR` constraints hold there,
  (3) the selector columns are one-hot at `st`.
* `rowLocal_of_rowMatch`: the 72 row-local packed gates (`paperPackingRowLocal`) vanish at such an env
  (A-free copy of the row-local half of `exact_finalNonIOSourceFamilies17`, through
  `paperPacking_iff_atomic`).
* `eval_congr_typed`: read-set congruence of typed sources over `LnRead.roles/chals`.
* `towerHolds_rowLocal`: for every kept core id `i < 72` (the 69 row-local ids), the gate holds in
  `𝕂′` at `towerEnv309`, given a full source env `E` satisfying `RowMatch` that agrees with the tower
  env off the dead read set (roles `54`, `55`, challenges `0`, `9`; justified by `LnRead.kept_no_ln`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Reified Nock.ComputeTable
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.ComputePaperPacking (OneHotSelector paperPacking_iff_atomic)
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.T0TowerFP
open Nock.NockVMROM.Thm54.Unhosted309

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 300000

noncomputable section

section RowMatch
variable {K : Type} [Field K]

/-- **The restated hypotheses (1)-(3) of DESIGN §(a)** on an arbitrary source environment. -/
structure RowMatch (env : Env K) (inp : Inputs K) (st : State) (pub : Pub K) (dec : Dec K)
    (ex : Extra K) : Prop where
  table : ∀ j, j < 94 → (Env.ofSubst computeSubst env).trace j =
    (computeEnvFull inp (opSel st) pub dec ex).trace j
  chal : ∀ j, j < 5 → (Env.ofSubst computeSubst env).chal j =
    (computeEnvFull inp (opSel st) pub dec ex).chal j
  pubs : ∀ j, env.pub j = (computeEnvFull inp (opSel st) pub dec ex).pub j
  air : ∀ c ∈ Nock.Reified.computeAIR.constraints,
    c.expr.eval (computeEnvFull inp (opSel st) pub dec ex) = 0
  oneHot : OneHotSelector env st

variable {env : Env K} {inp : Inputs K} {st : State} {pub : Pub K} {dec : Dec K} {ex : Extra K}

/-- (A-free `exact_computeAIR_row_substituted`.) -/
theorem RowMatch.air_subst (h : RowMatch env inp st pub dec ex) :
    ∀ c ∈ Nock.Reified.computeAIR.constraints, (c.expr.subst computeSubst).eval env = 0 := by
  intro c hc
  rw [eval_computeSubst]
  rw [CurrentComputeExpr.eval_eq (computeAIR_current_footprint c hc) h.table h.chal
    (fun j => by simpa [Env.ofSubst, computeSubst, Expr.eval] using h.pubs j)]
  exact h.air c hc

variable [Fintype K] [DecidableEq K]

/-- (A-free `exact_refoldedPerStateGates`.) -/
theorem RowMatch.refolded (h : RowMatch env inp st pub dec ex) :
    ∀ e ∈ refoldedPerStateGates, e.eval env = 0 := by
  have hair := h.air_subst
  have hmap :
      ∀ e ∈ Nock.Reified.perStateGated.map (fun e => e.subst computeSubst), e.eval env = 0 := by
    intro e he
    obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp he
    apply hair ⟨.row, src⟩
    simp [Nock.Reified.computeAIR, hsrc]
  have hfix := fixed_overlay_leaf_booleanity_degrees
  have hop3mem :
      op3ELeafBool.subst computeSubst ∈
        Nock.Reified.perStateGated.map (fun e => e.subst computeSubst) := by
    apply List.mem_map.mpr
    refine ⟨op3ELeafBool, ?_, rfl⟩
    rw [← hfix.1]
    exact List.get_mem _ _
  have hop5mem :
      op5ELeafBool.subst computeSubst ∈
        Nock.Reified.perStateGated.map (fun e => e.subst computeSubst) := by
    apply List.mem_map.mpr
    refine ⟨op5ELeafBool, ?_, rfl⟩
    rw [← hfix.2.1]
    exact List.get_mem _ _
  have hop3 : op3ELeafBoolRefold.eval env = 0 := by
    rw [← op3ELeafBool_refold_eval_oneHot env st h.oneHot]
    exact hmap _ hop3mem
  have hop5 : op5ELeafBoolRefold.eval env = 0 := by
    rw [← op5ELeafBool_refold_eval_oneHot env st h.oneHot]
    exact hmap _ hop5mem
  rw [refoldedPerStateGates]
  exact all_mem_set_zero env _ 270 op5ELeafBoolRefold
    (all_mem_set_zero env _ 177 op3ELeafBoolRefold hmap hop3) hop5

/-- **`rowLocal_of_rowMatch`**: the 72 row-local packed gates vanish at any env satisfying (1)-(3). -/
theorem rowLocal_of_rowMatch (h : RowMatch env inp st pub dec ex) :
    ∀ g ∈ paperPackingRowLocal, g.eval env = 0 := by
  have hair := h.air_subst
  have hz : (zZinvExpr.subst computeSubst).eval env = 0 :=
    hair ⟨.row, zZinvExpr⟩ (by simp [Nock.Reified.computeAIR])
  have hrefold := h.refolded
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (paperPacking_iff_atomic env st h.oneHot hz).2
      (fun s e he => hrefold e (stateBlock_mem_refolded s e he)) g hg
  · simp only [alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hg
    rcases hg with (rfl | rfl | rfl) | ⟨src, hsrc, rfl⟩
    · exact hair ⟨.row, sv4Expr⟩ (by simp [Nock.Reified.computeAIR, svExprs])
    · exact hair ⟨.row, sv5Expr⟩ (by simp [Nock.Reified.computeAIR, svExprs])
    · exact hair ⟨.row, sv6Expr⟩ (by simp [Nock.Reified.computeAIR, svExprs])
    · exact hair ⟨.row, src⟩ (by simp [Nock.Reified.computeAIR, hsrc])

end RowMatch

/-! ## Read-set congruence over the typed sources -/

section Congr
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Two typed environments agree off the dead read set (publics are NOT compared; see `correctedPublicFreeB` below): everything but extension roles `54`/`55` and
challenges `0`/`9` is equal. -/
structure AgreeOff (E₁ E₂ : CorrectedFinalTypedEnv F K) : Prop where
  baseTrace : E₁.baseTrace = E₂.baseTrace
  baseTraceNext : E₁.baseTraceNext = E₂.baseTraceNext
  extTraceNext : E₁.extTraceNext = E₂.extTraceNext
  certBase : E₁.certBase = E₂.certBase
  certExt : E₁.certExt = E₂.certExt
  expCol : E₁.expCol = E₂.expCol
  ext : ∀ r : Fin 63, r.val ≠ 54 → r.val ≠ 55 → E₁.extTrace r = E₂.extTrace r
  chal : ∀ s : Fin 12, s.val ≠ 0 → s.val ≠ 9 → E₁.chal s = E₂.chal s

/-- **`eval_congr_reads` (typed form)**: a typed source whose `LnRead` read set avoids roles `54`/`55`
and challenges `0`/`9` evaluates identically at two environments agreeing off them. -/
theorem eval_congr_reads_typed {E₁ E₂ : CorrectedFinalTypedEnv F K} (h : AgreeOff E₁ E₂) :
    ∀ t : CorrectedFinalTypedExpr, touchesT t = false → OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB t = true →
      t.eval E₁ = t.eval E₂ := by
  intro t
  induction t with
  | baseCur i => intro _ _; simp [CorrectedFinalTypedExpr.eval, h.baseTrace]
  | baseNext i => intro _ _; simp [CorrectedFinalTypedExpr.eval, h.baseTraceNext]
  | extCur i =>
      intro ht _
      simp only [touchesT, roles, chals, Bool.or_eq_false_iff, List.any_eq_false] at ht
      have := ht.1 i.val (by simp)
      simp only [CorrectedFinalTypedExpr.eval]
      exact h.ext i (fun e => this (by simp [e])) (fun e => this (by simp [e]))
  | extNext i => intro _ _; simp [CorrectedFinalTypedExpr.eval, h.extTraceNext]
  | challenge i =>
      intro ht _
      simp only [touchesT, roles, chals, Bool.or_eq_false_iff, List.any_eq_false] at ht
      have := ht.2 i.val (by simp)
      simp only [CorrectedFinalTypedExpr.eval]
      exact h.chal i (fun e => this (by simp [e])) (fun e => this (by simp [e]))
  | extensionPublic i => intro _ hp; simp [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB] at hp
  | scalarPublic i => intro _ hp; simp [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB] at hp
  | const c => intro _ _; rfl
  | add x y ihx ihy =>
      intro ht hp
      simp only [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB, Bool.and_eq_true] at hp
      simp only [touchesT, roles, chals, Bool.or_eq_false_iff, List.any_eq_false,
        List.mem_append] at ht
      simp only [CorrectedFinalTypedExpr.eval]
      rw [ihx (by simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false]
                  exact ⟨fun a ha => ht.1 a (Or.inl ha), fun a ha => ht.2 a (Or.inl ha)⟩) hp.1,
        ihy (by simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false]
                exact ⟨fun a ha => ht.1 a (Or.inr ha), fun a ha => ht.2 a (Or.inr ha)⟩) hp.2]
  | sub x y ihx ihy =>
      intro ht hp
      simp only [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB, Bool.and_eq_true] at hp
      simp only [touchesT, roles, chals, Bool.or_eq_false_iff, List.any_eq_false,
        List.mem_append] at ht
      simp only [CorrectedFinalTypedExpr.eval]
      rw [ihx (by simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false]
                  exact ⟨fun a ha => ht.1 a (Or.inl ha), fun a ha => ht.2 a (Or.inl ha)⟩) hp.1,
        ihy (by simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false]
                exact ⟨fun a ha => ht.1 a (Or.inr ha), fun a ha => ht.2 a (Or.inr ha)⟩) hp.2]
  | mul x y ihx ihy =>
      intro ht hp
      simp only [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB, Bool.and_eq_true] at hp
      simp only [touchesT, roles, chals, Bool.or_eq_false_iff, List.any_eq_false,
        List.mem_append] at ht
      simp only [CorrectedFinalTypedExpr.eval]
      rw [ihx (by simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false]
                  exact ⟨fun a ha => ht.1 a (Or.inl ha), fun a ha => ht.2 a (Or.inl ha)⟩) hp.1,
        ihy (by simp only [touchesT, Bool.or_eq_false_iff, List.any_eq_false]
                exact ⟨fun a ha => ht.1 a (Or.inr ha), fun a ha => ht.2 a (Or.inr ha)⟩) hp.2]
  | neg x ih =>
      intro ht hp
      simp only [CorrectedFinalTypedExpr.eval]
      rw [ih (by simpa only [touchesT, roles, chals] using ht)
        (by simpa only [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB] using hp)]
  | pow x n ih =>
      intro ht hp
      simp only [CorrectedFinalTypedExpr.eval]
      rw [ih (by simpa only [touchesT, roles, chals] using ht)
        (by simpa only [OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB] using hp)]
  | certBase i => intro _ _; simp [CorrectedFinalTypedExpr.eval, h.certBase]
  | certExt i => intro _ _; simp [CorrectedFinalTypedExpr.eval, h.certExt]
  | lamPow d =>
      intro ht _
      simp [touchesT, chals] at ht
  | expCur => intro _ _; simp [CorrectedFinalTypedExpr.eval, h.expCol]

end Congr

/-! ## The tower statement -/

section Tower
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
variable (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The first 72 production ext gates are the 72 row-local packed gates. -/
theorem finalExt_get_rowLocal (i : ℕ) (hi : i < 72) (h : i < finalExtTransitionGates.length) :
    finalExtTransitionGates[i] ∈ paperPackingRowLocal := by
  have hl : i < paperPackingRowLocal.length := by rw [paperPackingRowLocal_length]; exact hi
  have : finalExtTransitionGates[i] = paperPackingRowLocal[i] := by
    simp only [finalExtTransitionGates, paperPacking_eq_rowLocal_append]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left hl]
  rw [this]
  exact List.getElem_mem hl

theorem keptCore_lt72_not_special (i : CorrectedCoreExtGateId) (h : i.val < 72) :
    specialCore i = false := by
  simp [specialCore]; omega

/-- **The 69 row-local kept gates read no public** (`.extensionPublic` / `.scalarPublic`). -/
theorem rowLocal_kept_publicFree :
    ∀ i ∈ keptCoreIdsQ7, i.val < 72 →
      OptimizedComputeCanonicalSatisfaction.correctedPublicFreeB (correctedFinalExtGate i) = true := by
  decide +kernel

/-- **C2a: the row-local kept core gates hold in `𝕂′` at the tower environment.**
`E` is a full source-layout env over `𝕂′` (the honest source env, with a free generator `α*` in the
dead roles `54`/`55` and challenge `0`) satisfying the restated hypotheses (1)-(3) (`RowMatch`) and
agreeing with the tower base env off the dead read set.  Conclusion: every kept core id `i < 72`
(the 69 ids `0..71` minus `{50, 58, 65}`) holds at `towerEnv309`. -/
theorem towerHolds_rowLocal (eK : Env K) (eF : Env F)
    (E : CorrectedFinalTypedEnv F (Quad (algebraMap F K δ)))
    {inp : Inputs (Quad (algebraMap F K δ))} {st : State} {pub : Pub (Quad (algebraMap F K δ))}
    {dec : Dec (Quad (algebraMap F K δ))} {ex : Extra (Quad (algebraMap F K δ))}
    (hM : RowMatch E.toSourceEnv inp st pub dec ex)
    (hag : AgreeOff (towerEnv309 δ towerM eK eF).base E)
    (i : CorrectedCoreExtGateId) (hi : i ∈ keptCoreIdsQ7) (hlt : i.val < 72) :
    towerHolds δ eK eF (coreTarget i) := by
  classical
  have hns := keptCore_lt72_not_special i hlt
  have hn : coreTouches i = false := kept_no_ln.1 i hi
  have hn' : touchesT (correctedFinalExtGate i) = false := by
    have hne1 : i ≠ packedQueueNonEmptyId := by intro e; rw [e] at hlt; simp at hlt
    have hne2 : i ≠ packedQueueTilingId := by intro e; rw [e] at hlt; simp at hlt
    have hne3 : i ≠ packedWalkCountId := by intro e; rw [e] at hlt; simp at hlt
    have hne4 : i ≠ packedWalkAccId := by intro e; rw [e] at hlt; simp at hlt
    have hne5 : i ≠ packedChainId := by intro e; rw [e] at hlt; simp at hlt
    simpa [coreTouches, hne1, hne2, hne3, hne4, hne5] using hn
  have hct : coreTarget i = .leaf (correctedFinalExtGate i) := by simp [coreTarget, hns]
  rw [hct]
  show (correctedFinalExtGate i).eval (towerEnv309 δ towerM eK eF).base = 0
  rw [eval_congr_reads_typed hag _ hn' (rowLocal_kept_publicFree i hi hlt), ← correctedFinalExtGate_eval_source E i]
  exact rowLocal_of_rowMatch hM _ (finalExt_get_rowLocal i hlt (by simp))

/-- The 69 row-local kept ids. -/
theorem rowLocal_kept_count :
    (keptCoreIdsQ7.filter fun i => decide (i.val < 72)).length = 69 := by decide +kernel

/-- A typed env with its publics zeroed (what `RowMatch.pubs` demands). -/
def zeroPub {F K : Type} [Field F] [Field K] (T : CorrectedFinalTypedEnv F K) :
    CorrectedFinalTypedEnv F K :=
  { T with extensionPublic := fun _ => 0, scalarPublic := fun _ => 0 }

theorem zeroPub_pub {F K : Type} [Field F] [Field K] [Algebra F K] (T : CorrectedFinalTypedEnv F K) (j : ℕ) :
    (zeroPub T).toSourceEnv.pub j = 0 := by
  simp [zeroPub, CorrectedFinalTypedEnv.toSourceEnv]

theorem agreeOff_zeroPub {F K : Type} [Field F] [Field K] (T : CorrectedFinalTypedEnv F K) :
    AgreeOff T (zeroPub T) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **Sanity check (the publics conflict is gone).**  At a tower env whose scalar publics are NOT all
zero, the zero-publics source env `zeroPub T` (which satisfies the `pubs` clause, `zeroPub_pub`) agrees
off the dead read set, and `towerHolds_rowLocal` applies. -/
theorem towerHolds_rowLocal_nonzeroPub (eK : Env K) (eF : Env F)
    (hnz : ∃ j, (towerEnv309 δ towerM eK eF).base.scalarPublic j ≠ 0)
    {inp : Inputs (Quad (algebraMap F K δ))} {st : State} {pub : Pub (Quad (algebraMap F K δ))}
    {dec : Dec (Quad (algebraMap F K δ))} {ex : Extra (Quad (algebraMap F K δ))}
    (hM : RowMatch (zeroPub (towerEnv309 δ towerM eK eF).base).toSourceEnv inp st pub dec ex)
    (i : CorrectedCoreExtGateId) (hi : i ∈ keptCoreIdsQ7) (hlt : i.val < 72) :
    (zeroPub (towerEnv309 δ towerM eK eF).base).scalarPublic ≠
        (towerEnv309 δ towerM eK eF).base.scalarPublic ∧
      (∀ j, (zeroPub (towerEnv309 δ towerM eK eF).base).toSourceEnv.pub j = 0) ∧
      towerHolds δ eK eF (coreTarget i) := by
  refine ⟨?_, zeroPub_pub _, towerHolds_rowLocal δ eK eF _ hM (agreeOff_zeroPub _) i hi hlt⟩
  obtain ⟨j, hj⟩ := hnz
  intro h
  exact hj (by simpa [zeroPub] using (congrFun h j).symm)

end Tower

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
