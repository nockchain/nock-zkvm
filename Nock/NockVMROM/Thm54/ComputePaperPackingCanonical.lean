import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction

/-!
Split from `ComputePaperPacking.lean` so the exactness lemmas can be imported by
`OptimizedComputeSameExecution` without a cycle through this canonical section.
-/

namespace Nock.NockVMROM.Thm54
namespace ComputePaperPacking

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

open Nock
open Nock.Reified
open Nock.ComputeTable
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis
open OptimizedComputeFinalTypedLowering
open OptimizedComputeCorrectedFinal
open OptimizedComputeTemplate

/-! ## 12. Canonical satisfaction

The honest same-execution rows and the gathered canonical polynomial trace satisfy every
coin-free gate.  The 73 row-local gates (`paperPackingRowLocal`) hold on **every** row including
the terminal one; the four cross-row singletons hold on every row with a successor, exactly as
the deployed chip masks them at the last row (`OptimizedComputeCorrectedFinal.correctedCoreCoord`
ids `73..76`). -/

theorem alwaysOn_mem_terminalCurrent :
    ∀ g ∈ alwaysOnOptimized,
      g ∈ OptimizedComputeSameExecution.terminalCurrentNonIOSourceFamilies.flatten := by
  decide

theorem zZinv_mem_terminalCurrent :
    zZinvExpr.subst computeSubst ∈
      OptimizedComputeSameExecution.terminalCurrentNonIOSourceFamilies.flatten := by
  decide

/-- Every row-local gate lowers to a typed expression that reads only current base columns,
extension roles `< 58`, challenges — and no public (the receipt the gathered-trace lift needs). -/
theorem paperPackingRowLocal_lower_receipt :
    ∀ e ∈ paperPackingRowLocal,
      OptimizedComputeCanonicalSatisfaction.terminalCurrentSourceGood e = true := by
  decide

/-- Packed production slots `72..75` are the four cross-row singletons themselves (no fold). -/
theorem crossRow_packed_slots (j : Fin 4) :
    finalExtTransitionGates.get ⟨72 + (j : ℕ), by simp; have := j.isLt; omega⟩ =
      crossRowSingletons.get ⟨j, by
        simp [crossRowSingletons, OptimizedComputeGateBasis.crossRowSingletons]⟩ := by
  fin_cases j <;> decide

theorem finalRlcFold_singleton_eval {K : Type*} [Field K] (env : Env K) (g : Expr) :
    (finalRlcFold [g]).eval env = g.eval env := by
  simp [finalRlcFold, Expr.eval]

section Canonical

open Nock.Framework Reify
open Module
open OptimizedComputeFinal
open OptimizedComputeFinalTrace
open OptimizedComputeSemanticRealization
open OptimizedComputeSameExecution
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeSampledTrace
open OptimizedComputeOverlay
open StrictExtension
open CoordinateBasis
open CoordinateCompiler
open OptimizedComputeBaseGates
open MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K] [DecidableEq F]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- The honest row's selector is the one-hot of its opcode (successor-free view). -/
theorem exactFinalCurrentEnv_oneHot
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows) :
    OneHotSelector (exactFinalCurrentEnv A i).toSourceEnv
      (R.problem.exec.computePubAt i).state :=
  fun s => exactFinalCurrentEnv_selectors A i s

theorem exactFinalTransitionEnv_oneHot
    (A : SampledIOSameExecutionAssignment R p) (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    OneHotSelector (exactFinalTransitionEnv A i hi).toSourceEnv
      (R.problem.exec.computePubAt i).state :=
  fun s => exactFinalTransitionEnv_selectors A i hi s

/-- **Honest satisfaction, every row**: the 73 row-local coin-free gates vanish on the exact
successor-free row (`exact_refoldedPerStateGates_current` through `paperPacking_iff_atomic`). -/
theorem exact_paperPackingRowLocal_current
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) :
    ∀ g ∈ paperPackingRowLocal, g.eval (exactFinalCurrentEnv A i).toSourceEnv = 0 := by
  have hterm := exact_terminalCurrentNonIOSourceFamilies A h i
  have hsel := exactFinalCurrentEnv_oneHot A i
  have hz := hterm _ zZinv_mem_terminalCurrent
  have hrefold := exact_refoldedPerStateGates_current A h i
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (paperPacking_iff_atomic _ _ hsel hz).2
      (fun s e he => hrefold e (stateBlock_mem_refolded s e he)) g hg
  · exact hterm g (alwaysOn_mem_terminalCurrent g hg)

/-- **Honest satisfaction, rows with a successor**: the 76 core coin-free gates vanish on the
exact transition environment (`exact_finalNonIOSourceFamilies17` through
`paperPacking_iff_sources`). -/
theorem exact_paperPackingNonIOGates_transition
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    ∀ g ∈ paperPackingCoreGates, g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0 := by
  have hsrc := exact_finalNonIOSourceFamilies17 A h i hi
  exact (paperPacking_iff_sources _ _ (exactFinalTransitionEnv_oneHot A i hi)
      (hsrc _ zZinv_mem_finalNonIO)).2 hsrc

/-- The honest transition row is collision-free, so the deployed folds and the *core*
coin-free set agree there in both directions. -/
theorem exact_deployed_iff_paperPacking_transition
    (A : SampledIOSameExecutionAssignment R p)
    (h : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    (∀ g ∈ finalNonIOTransitionGates, g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0) ↔
      (∀ g ∈ paperPackingCoreGates, g.eval (exactFinalTransitionEnv A i hi).toSourceEnv = 0) :=
  ⟨paperPacking_of_deployed _ _ (exactFinalTransitionEnv_oneHot A i hi)
      (exact_finalComputeCollisionFree A h i hi),
   fun hg => deployed_of_paperPacking _ _ (exactFinalTransitionEnv_oneHot A i hi)
      (exact_finalNonIOSourceFamilies17 A h i hi _ zZinv_mem_finalNonIO) hg⟩

/-- **Canonical polynomial trace, every row**: the 73 row-local gates vanish on the gathered
environment of `correctedCanonicalFinalTrace` at any node (the
`canonical_terminalCurrentNonIOSourceFamilies` lift, generalised off the last row). -/
theorem canonical_paperPackingRowLocal
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (i : Fin R.problem.cfg.compRows)
    (e : Expr) (he : e ∈ paperPackingRowLocal) :
    let can := gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)
    e.eval can.toSourceEnv = 0 := by
  dsimp only
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
  let ex := exactFinalCurrentEnv A i
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with
      extensionPublic := can.extensionPublic
      scalarPublic := can.scalarPublic }
  have hg := paperPackingRowLocal_lower_receipt e he
  obtain ⟨t, htLower, htCurrent, htPublic⟩ :
      ∃ t, correctedLowerFinal e = some t ∧
        CorrectedTerminalCurrentOnly t ∧ CorrectedPublicFree t := by
    cases ht : correctedLowerFinal e with
    | none => simp [terminalCurrentSourceGood, ht] at hg
    | some t =>
        simp [terminalCurrentSourceGood, ht] at hg
        exact ⟨t, rfl, (correctedTerminalCurrentOnlyB_iff t).1 hg.1,
          (correctedPublicFreeB_iff t).1 hg.2⟩
  rw [correctedLowerFinal_eval can e t htLower]
  have hsame : t.eval can = t.eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_terminalCurrentOnly
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i q
    · intro role hrole
      let r : Fin 58 := ⟨role, hrole⟩
      have hc := canonical_gather_ext_core
        A hn nodes hnodes b chalVal pubVal orbit i r
      have heq : exPub.extTrace role = coreExtensionValue (encodedRowAt A i) r := by
        simp [exPub, ex, exactFinalCurrentEnv, exactFinalExtensionRow, hrole, r]
      have hc' : can.extTrace role = coreExtensionValue (encodedRowAt A i) r := by
        simpa [can, r, OptimizedComputeFinalTrace.formRLeafCore] using hc
      exact hc'.trans heq.symm
    · intro q
      simpa [can, exPub, ex, exactFinalCurrentEnv] using
        canonical_gather_challenge A hn nodes b chalVal pubVal orbit hchal i q
    · intro q; rfl
    · intro q; rfl
    · exact htCurrent
  have hpub : t.eval exPub = t.eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree
    all_goals first | exact htPublic | (intro q; rfl) | rfl
  rw [hsame, hpub, ← correctedLowerFinal_eval ex e t htLower]
  exact exact_paperPackingRowLocal_current A hA i e he

/-- **Canonical polynomial trace, rows with a successor**: the four cross-row singletons vanish,
read off the deployed slots `8..11` (`canonical_ext_gate_nonterminal_zero`), whose folds are
`g + c₉ · 0`. -/
theorem canonical_crossRowSingletons_nonterminal
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound A b)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (g : Expr) (hg : g ∈ crossRowSingletons) :
    let can := gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)
    g.eval can.toSourceEnv = 0 := by
  dsimp only
  obtain ⟨n, hn4⟩ := List.get_of_mem hg
  let j : Fin 4 := ⟨n, Nat.lt_of_lt_of_eq n.isLt
      (by simp [crossRowSingletons, OptimizedComputeGateBasis.crossRowSingletons])⟩
  have hext := canonical_ext_gate_nonterminal_zero
    A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hax hwidth hord i hi
    ⟨72 + (j : ℕ), by have := j.isLt; omega⟩
  dsimp only at hext
  have hsrc := correctedFinalExtGate_eval_source
    (gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal))
    ⟨72 + (j : ℕ), by have := j.isLt; omega⟩
  rw [hext, crossRow_packed_slots j] at hsrc
  have hget : crossRowSingletons.get ⟨(j : ℕ), by
      simp [crossRowSingletons, OptimizedComputeGateBasis.crossRowSingletons]⟩ = g := by
    convert hn4
  rw [hget] at hsrc
  exact hsrc

/-- **All 77 coin-free gates on every canonical row with a successor.** -/
theorem canonical_paperPackingNonIOGates_nonterminal
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hstep : ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound A b)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows) :
    let can := gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)
    ∀ g ∈ paperPackingNonIOGates, g.eval can.toSourceEnv = 0 := by
  dsimp only
  intro g hg
  rw [paperPackingNonIOGates_eq_rowLocal_append] at hg
  change g ∈ (paperPackingRowLocal ++ crossRowSingletons) ++
      OptimizedComputeGateBasis.queueWitnessGates at hg
  rcases List.mem_append.mp hg with hg | hgq
  · rcases List.mem_append.mp hg with hrow | hcross
    · exact canonical_paperPackingRowLocal A hA hn nodes hnodes b chalVal pubVal orbit
        hchal i g hrow
    · exact canonical_crossRowSingletons_nonterminal A hA hn nodes hnodes b chalVal pubVal
        orbit hstep hchal hax hwidth hord i hi g hcross
  · have hgate :=
      OptimizedComputeCanonicalSatisfaction.canonical_ext_gate_nonterminal_zero
        A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hax hwidth hord i hi
    simp [OptimizedComputeGateBasis.queueWitnessGates] at hgq
    rcases hgq with rfl | rfl
    · have hext := hgate packedQueueNonEmptyId
      dsimp only at hext
      have hsrc := correctedFinalExtGate_eval_source
        (gatherCorrectedFinalTypedEnv b
          (envOfTrace
            (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
            orbit.ω (nodes i) chalVal pubVal))
        packedQueueNonEmptyId
      rw [hext, OptimizedComputeCanonicalSatisfaction.packedQueueNonEmpty_source] at hsrc
      exact hsrc
    · have hext := hgate packedQueueTilingId
      dsimp only at hext
      have hsrc := correctedFinalExtGate_eval_source
        (gatherCorrectedFinalTypedEnv b
          (envOfTrace
            (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
            orbit.ω (nodes i) chalVal pubVal))
        packedQueueTilingId
      rw [hext, OptimizedComputeCanonicalSatisfaction.packedQueueTiling_source] at hsrc
      exact hsrc

/-- **The two coin-free walk-initial gates hold on every canonical row**: on row `0` from
`canonical_walk_endpoint_sources`, elsewhere the `isFirst` mask is `0`. -/
theorem canonical_walkInitUnfolded
    [FiniteDimensional F K]
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {hgt : ℕ} (orbit : StrictOrbitDomain F 3 hgt)
    (hchal : ExactFinalChallengeCoordinates b A chalVal)
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (i : Fin R.problem.cfg.compRows) :
    let env := gatherCorrectedFinalTypedEnv b
      (envOfTrace
        (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
        orbit.ω (nodes i) chalVal pubVal)
    ∀ g ∈ walkInitUnfolded, g.eval env.toSourceEnv = 0 := by
  dsimp only
  let env := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
  have hend := canonical_walk_endpoint_sources
    A hA hn nodes hnodes b chalVal pubVal orbit (fun k => hchal 6 k) (fun k => hchal 10 k) hpub
  have hb11 := canonical_gather_base_current
    A hn nodes hnodes b chalVal pubVal orbit i (11 : Fin 13)
  intro g hg
  simp only [walkInitUnfolded, List.mem_cons, List.not_mem_nil, or_false] at hg
  by_cases hi0 : (i : ℕ) = 0
  · have hiEq : i = ⟨0, hn⟩ := Fin.ext hi0
    subst hiEq
    have hb1 : env.baseTrace 11 = 1 := by
      have hx := hb11
      simpa [env, finalBaseCell] using hx
    have hm : fixedIsFirst.eval env.toSourceEnv = 1 := by
      simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb1]
    rcases hg with rfl | rfl
    · simp only [finalMaskedWalkLn1, Expr.eval]
      rw [hm, hend.1]
      ring
    · simp only [finalMaskedWalkCount1, Expr.eval]
      rw [hm, hend.2.1]
      ring
  · have hb0 : env.baseTrace 11 = 0 := by
      simpa [env, finalBaseCell, hi0] using hb11
    have hm : fixedIsFirst.eval env.toSourceEnv = 0 := by
      simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv, hb0]
    rcases hg with rfl | rfl
    · simp only [finalMaskedWalkLn1, Expr.eval]
      rw [hm, zero_mul]
    · simp only [finalMaskedWalkCount1, Expr.eval]
      rw [hm, zero_mul]

end
end Canonical

#print axioms exact_paperPackingRowLocal_current
#print axioms exact_paperPackingNonIOGates_transition
#print axioms exact_deployed_iff_paperPacking_transition
#print axioms canonical_paperPackingRowLocal
#print axioms canonical_paperPackingNonIOGates_nonterminal
#print axioms canonical_walkInitUnfolded

end ComputePaperPacking
end Nock.NockVMROM.Thm54
