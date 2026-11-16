import Nock.NockVMROM.Thm54.OptimizedStrictPackage

/-!
# From the merged memory sources back to `memoryAIR`

Two directions are involved and only one of them was compiled by the merge itself.

* **Forward** (`memoryAIR` ⟹ merged sources) is
  `OptimizedMemoryGateBasis.mergedMemoryConstraints_eval_zero`
  (`OptimizedMemoryGateBasis.lean:181`).  It needs no hypothesis at all, and it is what the
  shipped artifacts consume, through
  `OptimizedMemoryCanonicalSatisfaction.canonical_memoryRowSources`.
* **Backward** (merged sources ⟹ `memoryAIR`) was represented only by
  `MemoryFactorizationScope.mergedMemCore_iff_perStateGated`
  (`MemoryFactorizationScope.lean:366`), which *assumes* a one-hot selector
  (`MemoryFactorizationScope.SelectorOneHot`) rather than deriving one, and which has no
  consumer.  This module closes that hole: it derives the selector from the five retained
  State-Variables sources and lands the backward direction on the sources themselves.

## Why a characteristic condition appears, and why nothing is lost

The retained selector sources are booleanity plus `Σ op = 1` (`Nock/AIR.lean:1666`, `:1671`),
and **"boolean + sum one ⇒ one-hot" is false in small characteristic** — the tree already knows
this: `MemoryTable.oneHot_of_bool_sum` (`Nock/MemoryTable.lean:396`) carries
`hchar : ∀ n ≤ 4, (n : K) = 1 → n = 1`.  With four states there are exactly two escapes:

* **three ones**, which needs `(2 : K) = 0`;
* **four ones** (the all-ones selector), which needs `(3 : K) = 0`.

`§1` proves that these are the only escapes.  `§3` then kills the second one *semantically*: at
`(3 : K) = 0` the all-ones selector plus the merged core plus the `z · zinv = 1` witness gate
(`Nock/AIR.lean:1496`) is **infeasible** — merged class `5` forces `trace 9 = 0`, class `15`
forces `trace 4 = 0`, and class `0` then forces `chal 0 = 0`, contradicting `z · zinv = 1`.

That leaves `(2 : K) ≠ 0` as the sole hypothesis of the headline `§4` theorem — and that is
already a **field of the shipped package**: `OptimizedStrictPackage.OptimizedMemoryRealizationAt`
carries `two_ne_zero : (2 : K) ≠ 0` (`OptimizedStrictPackage.lean:114`).  `§5` discharges the
hypothesis from that field, so **no characteristic the package admits is lost by the merge**.
-/

namespace Nock.NockVMROM.Thm54
namespace MergedSourceBridge

open Nock
open Nock.Reified
open Nock.Framework.Reify
open Nock.MemoryTable
open Nock.NockVMROM.Thm54.MemoryFactorizationScope
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

variable {K : Type} [Field K]

/-! ## §1  What booleanity and `Σ op = 1` actually force

Over the four memory states a boolean selector summing to `1` is one-hot
**unless** the characteristic is `2` (three ones) or `3` (four ones).  The `2` case is excluded by
hypothesis here — it is the package's own `two_ne_zero` — and the `3` case is carried explicitly
so that §3 can kill it. -/

theorem oneHot_or_char_three_all_ones (op : MState → K) (h2 : (2 : K) ≠ 0)
    (hb : ∀ j, op j = 0 ∨ op j = 1) (hsum : sum4 op = 1) :
    (∃ s, op = opSel s) ∨ ((3 : K) = 0 ∧ ∀ j, op j = 1) := by
  simp only [sum4] at hsum
  rcases hb MState.decompose with hd | hd <;> rcases hb MState.halt with hh | hh <;>
      rcases hb MState.read_root with hr | hr <;> rcases hb MState.verify_child with hv | hv <;>
      rw [hd, hh, hr, hv] at hsum
  all_goals
    first
      | (exfalso
         have hbad : (1 : K) = 0 := by
           first | linear_combination hsum | linear_combination -hsum
         exact one_ne_zero hbad)
      | (exfalso
         have hbad : (2 : K) = 0 := by
           first | linear_combination hsum | linear_combination -hsum
         exact h2 hbad)
      | (refine Or.inr ⟨?_, ?_⟩
         · first | linear_combination hsum | linear_combination -hsum
         · intro j; cases j <;> assumption)
      | (refine Or.inl ⟨MState.decompose, funext ?_⟩
         intro j; cases j <;> simp [opSel, hd, hh, hr, hv]
         done)
      | (refine Or.inl ⟨MState.halt, funext ?_⟩
         intro j; cases j <;> simp [opSel, hd, hh, hr, hv]
         done)
      | (refine Or.inl ⟨MState.read_root, funext ?_⟩
         intro j; cases j <;> simp [opSel, hd, hh, hr, hv]
         done)
      | (refine Or.inl ⟨MState.verify_child, funext ?_⟩
         intro j; cases j <;> simp [opSel, hd, hh, hr, hv])

/-- The escape is real, not a proof artefact: at characteristic `3` the all-ones selector
satisfies booleanity **and** `Σ op = 1`, and it is not one-hot. -/
theorem char_three_all_ones_passes_selector_sources :
    (∀ j : MState, (fun _ : MState => (1 : ZMod 3)) j * (1 - (fun _ : MState => (1 : ZMod 3)) j)
        = 0) ∧
      sum4 (fun _ : MState => (1 : ZMod 3)) = 1 ∧
      ∀ s : MState, (fun _ : MState => (1 : ZMod 3)) ≠ opSel s := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hs
  have := congrFun hs (match s with
    | MState.decompose => MState.halt
    | _ => MState.decompose)
  cases s <;> simp [opSel] at this

/-! ## §2  The five retained selector sources, read off the shipped source list -/

/-- Every merged constraint vanishes at the substituted environment whenever every shipped source
vanishes.  This is just `Expr.eval_subst` applied to `memoryRowSources`. -/
theorem mergedMemoryConstraints_eval_of_sources (env : Env K)
    (h : ∀ e ∈ memoryRowSources (K := K), e.eval env = 0) :
    ∀ e ∈ mergedMemoryConstraints (K := K), e.eval (Env.ofSubst memorySubst env) = 0 := by
  intro e he
  have := h (e.subst memorySubst) (List.mem_map.mpr ⟨e, he, rfl⟩)
  rwa [Expr.eval_subst] at this

/-- Booleanity of the four selector columns, from the shipped sources (`Nock/AIR.lean:1666`). -/
theorem sources_selector_bool (env : Env K)
    (hsv : ∀ e ∈ memSvExprs, e.eval (Env.ofSubst memorySubst env) = 0) (j : MState) :
    (tc (mopCol j)).eval (Env.ofSubst memorySubst env) = 0 ∨
      (tc (mopCol j)).eval (Env.ofSubst memorySubst env) = 1 := by
  have h := hsv (memSvBoolExprF (mopCol j))
    (List.mem_append_left _ (List.mem_map.mpr ⟨j, mem_allMStates j, rfl⟩))
  simp only [memSvBoolExprF, Expr.eval] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl h1
  · right; linear_combination -h1

/-- `Σ op = 1`, from the shipped sources (`Nock/AIR.lean:1671`). -/
theorem sources_selector_sum (env : Env K)
    (hsv : ∀ e ∈ memSvExprs, e.eval (Env.ofSubst memorySubst env) = 0) :
    sum4 (fun j => (tc (mopCol j)).eval (Env.ofSubst memorySubst env)) = 1 := by
  have h := hsv memSvOneHotExpr (List.mem_append_right _ List.mem_cons_self)
  simp only [memSvOneHotExpr, Expr.eval, mopCol, sum4] at h ⊢
  linear_combination h

/-! ## §3  Characteristic three: the all-ones selector is infeasible

`§1`'s second escape survives only if the merged core and the `z · zinv = 1` witness can be
satisfied at the all-ones selector.  They cannot. -/

theorem mergedGate_mem_mergedMemCore (q : ℕ) (h : q < 27) :
    mergedGate (K := K) q ∈ mergedMemCore (K := K) :=
  List.mem_map.mpr ⟨q, List.mem_range.mpr h, rfl⟩

/-- **At `(3 : K) = 0` the all-ones selector is infeasible.**  Merged class `5` forces
`trace 9 = 0`, class `15` forces `trace 4 = 0`, and class `0` then forces `chal 0 = 0`, which the
`z · zinv = 1` witness gate (`zZinvExprM`, `Nock/AIR.lean:1496`) refutes. -/
theorem char_three_all_ones_infeasible (h3 : (3 : K) = 0) (env : Env K)
    (hall : ∀ j : MState, (tc (mopCol j)).eval env = 1)
    (hcore : ∀ g ∈ mergedMemCore (K := K), g.eval env = 0)
    (hz : zZinvExprM.eval env = 0) : False := by
  have hd := hall .decompose
  have hh := hall .halt
  have hr := hall .read_root
  have hv := hall .verify_child
  simp only [mopCol, tc, Expr.eval] at hd hh hr hv
  have h5 := hcore _ (mergedGate_mem_mergedMemCore 5 (by norm_num))
  have h15 := hcore _ (mergedGate_mem_mergedMemCore 15 (by norm_num))
  have h0 := hcore _ (mergedGate_mem_mergedMemCore 0 (by norm_num))
  simp [mergedGate, memQuantity, paddedBlock, blockDecompose, blockHalt, blockReadRoot,
    blockVerifyChild, gateByM, mopCol, tc, chl, mPt, mLc, mRc, mMem,
    mrCol, fpCol, mconsExpr, Expr.eval, hd, hh, hr, hv] at h5 h15 h0
  simp only [zZinvExprM, Expr.eval, chl, tc] at hz
  have ht4 : env.trace 4 = 0 := by linear_combination -h15 + env.trace 23 * h3
  have hzz : env.chal 0 = 0 := by
    linear_combination -h0 + (4 : K) * ht4 - (env.trace 14 + 2) * h5
  rw [hzz] at hz
  simp at hz

/-! ## §4  The bridge -/

/-- Recovery of every `memoryAIR` constraint under an explicitly given one-hot selector.  This is
`MemoryFactorizationScope.mergedMemCore_iff_perStateGated` finally given a consumer, transported
to the shipped sources through `memorySubst`. -/
theorem recover_memoryAIR_of_selectorOneHot (env : Env K) (st : MState)
    (hone : SelectorOneHot (Env.ofSubst memorySubst env) st)
    (h : ∀ e ∈ memoryRowSources (K := K), e.eval env = 0) :
    ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (Env.ofSubst memorySubst env) = 0 := by
  have hsub := mergedMemoryConstraints_eval_of_sources env h
  have hsv : ∀ e ∈ memSvExprs, e.eval (Env.ofSubst memorySubst env) = 0 := fun e he =>
    hsub e (List.mem_append_left _ (List.mem_append_left _ he))
  have hz : zZinvExprM.eval (Env.ofSubst memorySubst env) = 0 :=
    hsub _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  have hcore : ∀ g ∈ mergedMemoryCore (K := K), (g.subst memorySubst).eval env = 0 := by
    intro g hg
    exact h (g.subst memorySubst) (List.mem_map.mpr ⟨g, List.mem_append_right _ hg, rfl⟩)
  have hgated : ∀ e ∈ memPerStateGated (K := K), e.eval (Env.ofSubst memorySubst env) = 0 :=
    (mergedMemoryCore_subst_iff_perStateGated env st hone).1 hcore
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
      exact hsv e he
    · rw [List.mem_singleton.mp hc]; exact hz
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact hgated e he

/-- **The bridge.**  Every constraint of the *pre-merge* row-local memory AIR
(`Nock.Reified.memoryAIR`, `Nock/AIR.lean:1748`, `75` constraints) is recovered from the *shipped
post-merge* source list (`OptimizedMemoryGateBasis.memoryRowSources`, `33` sources), with the
selector derived rather than assumed.

The only hypothesis is `(2 : K) ≠ 0`:

* characteristic `2` is excluded by that hypothesis, which is exactly the shipped package's own
  `OptimizedStrictPackage.OptimizedMemoryRealizationAt.two_ne_zero`
  (`OptimizedStrictPackage.lean:114`);
* characteristic `3` is *not* excluded — it is discharged by `char_three_all_ones_infeasible`,
  because there the only non-one-hot escape is infeasible against the merged core;
* every other characteristic is one-hot outright, by `oneHot_or_char_three_all_ones`.

Together with the forward direction `mergedMemoryConstraints_eval_zero`
(`OptimizedMemoryGateBasis.lean:181`) this makes "the merge cuts out the same solution set" a
compiled statement about the shipped objects, not about a scoping copy. -/
theorem merged_sources_recover_memoryAIR (env : Env K) (h2 : (2 : K) ≠ 0)
    (h : ∀ e ∈ memoryRowSources (K := K), e.eval env = 0) :
    ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (Env.ofSubst memorySubst env) = 0 := by
  have hsub := mergedMemoryConstraints_eval_of_sources env h
  have hsv : ∀ e ∈ memSvExprs, e.eval (Env.ofSubst memorySubst env) = 0 := fun e he =>
    hsub e (List.mem_append_left _ (List.mem_append_left _ he))
  rcases oneHot_or_char_three_all_ones
      (fun j => (tc (mopCol j)).eval (Env.ofSubst memorySubst env)) h2
      (sources_selector_bool env hsv) (sources_selector_sum env hsv) with
    ⟨st, hst⟩ | ⟨h3, hall⟩
  · refine recover_memoryAIR_of_selectorOneHot env st ?_ h
    intro j
    simpa [opSel] using congrFun hst j
  · exfalso
    have hz : zZinvExprM.eval (Env.ofSubst memorySubst env) = 0 :=
      hsub _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
    have hcore : ∀ g ∈ mergedMemCore (K := K), g.eval (Env.ofSubst memorySubst env) = 0 := fun g hg =>
      hsub g (List.mem_append_right _ ((mem_mergedMemoryCore_iff g).mpr hg))
    exact char_three_all_ones_infeasible h3 _ hall hcore hz

/-! ## §5  No characteristic the package admits is lost

The hypothesis of §4 is not an extra assumption bolted onto the merge: it is a field the shipped
memory realization already carries. -/

/-- **The package discharges the bridge's only hypothesis.**  Given any
`OptimizedStrictPackage.OptimizedMemoryRealizationAt` over `K`, the merged sources recover
`memoryAIR` with no side condition at all — so the merge loses no characteristic that the shipped
package admits. -/
theorem merged_sources_recover_memoryAIR_at_realization
    {F : Type} [Field F] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    {A : SampledIOSameExecutionAssignment R p}
    {execA : ExactExecution R.problem.cfg}
    {P : OptimizedMemorySameExecution.MemoryProductionAssignment A execA}
    {nodes : Fin R.problem.cfg.memRows → F}
    {b : Module.Basis (Fin 3) F K} {chalVal pubVal : ℕ → F}
    {h : ℕ} {orbit : StrictExtension.StrictOrbitDomain F 3 h}
    (hreal : OptimizedStrictPackage.OptimizedMemoryRealizationAt A P nodes b chalVal pubVal orbit)
    (env : Env K) (hsrc : ∀ e ∈ memoryRowSources (K := K), e.eval env = 0) :
    ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (Env.ofSubst memorySubst env) = 0 :=
  merged_sources_recover_memoryAIR env hreal.two_ne_zero hsrc

/-- **The shipped capstone package discharges it too.**  `OptimizedStrictNockVMROMPackage`
(`OptimizedStrictPackage.lean:229`) carries the same `two_ne_zero` field (`:281`), so any
package at all gives the bridge unconditionally. -/
theorem merged_sources_recover_memoryAIR_at_package
    {F : Type} [Field F] [Algebra F K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (pkg : OptimizedStrictPackage.OptimizedStrictNockVMROMPackage F K hOrb)
    (env : Env K) (hsrc : ∀ e ∈ memoryRowSources (K := K), e.eval env = 0) :
    ∀ c ∈ (memoryAIR (K := K)).constraints, c.expr.eval (Env.ofSubst memorySubst env) = 0 :=
  merged_sources_recover_memoryAIR env pkg.two_ne_zero hsrc

end MergedSourceBridge
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MergedSourceBridge.oneHot_or_char_three_all_ones
#print axioms Nock.NockVMROM.Thm54.MergedSourceBridge.char_three_all_ones_infeasible
#print axioms Nock.NockVMROM.Thm54.MergedSourceBridge.merged_sources_recover_memoryAIR
#print axioms Nock.NockVMROM.Thm54.MergedSourceBridge.merged_sources_recover_memoryAIR_at_realization
#print axioms Nock.NockVMROM.Thm54.MergedSourceBridge.merged_sources_recover_memoryAIR_at_package
