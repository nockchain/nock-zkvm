/-
  Nock/NockVMROM/Thm54/P8Core/FamilyComputeRows.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.FamilyComputeRows`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/FamilyComputeRows.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.DeployedComputeRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyComputeRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedComputeBaseGates
open OptimizedComputeFinal
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open ComputePaperPacking
open DeployedComputeRows
open DeployedChipFamily
open CoordinateBasis
open CoordinateCompiler
open Module
open MonolithicRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Family-chip gather of `Qc` at tuple `c`.  Mentions `Qc`. -/
def rowEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv P.optimized.basis
    (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c))

/-- Slot `q` of the family environment is `computeKOfTuple c q`. -/
theorem rowEnvAt_chal
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (q : Fin 12) :
    (rowEnvAt P c Qc i).toSourceEnv.chal q.val = computeKOfTuple c q.val := by
  have hq : (q : ℕ) < 12 := q.isLt
  simp only [CorrectedFinalTypedEnv.toSourceEnv, rowEnvAt, gatherCorrectedFinalTypedEnv,
    envOfTrace, hq, ↓reduceDIte]
  change (∑ k : Fin 3,
      computeChalValOfTuple P.optimized.basis c (3 * (q : ℕ) + (k : ℕ)) •
        P.optimized.basis k) =
    computeKOfTuple c q.val
  have hslot : ∀ k : Fin 3,
      3 * (q : ℕ) + (k : ℕ) < 36 := by
    intro k; omega
  have hcoord : ∀ k : Fin 3,
      computeChalValOfTuple P.optimized.basis c (3 * (q : ℕ) + (k : ℕ)) =
        coord P.optimized.basis (computeKOfTuple c q.val) k := by
    intro k
    simp only [computeChalValOfTuple, hslot k, ↓reduceIte]
    have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
    have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    apply congrArg
    exact Fin.ext hmod
  simp_rw [hcoord]
  exact reconstruct_coord P.optimized.basis (computeKOfTuple c q.val)

/-- A6: family compute chal 9 is the sampled `λ` (`computeKOfTuple` slot 9). -/
theorem rowEnvAt_chal9_lambda
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnvAt P c Qc i).toSourceEnv.chal 9 = c.2.2.2.lambda := by
  simpa [computeKOfTuple_lambda] using rowEnvAt_chal P c Qc i ⟨9, by decide⟩

theorem zZinv_at_rowEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hz : nprSeed c.1 ≠ 0) :
    (zZinvExpr.subst computeSubst).eval (rowEnvAt P c Qc i).toSourceEnv = 0 := by
  have h1 := rowEnvAt_chal P c Qc i ⟨1, by decide⟩
  have h5 := rowEnvAt_chal P c Qc i ⟨5, by decide⟩
  simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc, Expr.eval, h1, h5]
  exact sub_eq_zero.mpr (mul_inv_cancel₀ hz)

/-- Family and honest compute chips have the same width (`w = 199`).  The
projections do not unify (different `chalVal`), so callers `Fin.cast`. -/
theorem computeChipAt_width
    (c : OptimizedProductionChallengeTuple K F) :
    (P.computeChipAt c).rap.w = P.computeChip.rap.w := by
  have hc : (P.computeChipAt c).rap.w = 303 := by
    simp only [OptimizedFullStrictNockVMROMPackage.computeChipAt,
      DeployedChipFamily.computeChipAt, ProductionNamedComputeRAP]
    exact (corrected_rap_fingerprint P.optimized.basis
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)
      P.optimized.orbit (rowNodeSet P.optimized.computeNodes)).1
  have h0 : P.computeChip.rap.w = 303 := by
    simp only [OptimizedFullStrictNockVMROMPackage.computeChip,
      ProductionNamedComputeRAP]
    exact (corrected_rap_fingerprint P.optimized.basis
      P.optimized.computeChallenge P.optimized.computePublic
      P.optimized.orbit (rowNodeSet P.optimized.computeNodes)).1
  exact hc.trans h0.symm

/-- Family and honest memory chips have the same width (`w = 196`). -/
theorem memoryChipAt_width
    (c : OptimizedProductionChallengeTuple K F) :
    (P.memoryChipAt c).rap.w = P.memoryChip.rap.w := by
  have hc : (P.memoryChipAt c).rap.w = 205 := by
    simp only [OptimizedFullStrictNockVMROMPackage.memoryChipAt,
      DeployedChipFamily.memoryChipAt]
    exact (finalMemoryRAP_fingerprint
      P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).1
  have h0 : P.memoryChip.rap.w = 205 := by
    simp only [OptimizedFullStrictNockVMROMPackage.memoryChip]
    exact (finalMemoryRAP_fingerprint
      P.optimized.family.problem.cfg.memRows_pos P.optimized.memoryNodes
      P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      P.optimized.family.problem.cfg.kMem).1
  exact hc.trans h0.symm

/-- Reindex a constant-chip compute trace at the family width. -/
def familyQc
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin P.computeChip.rap.w → F[X]) :
    Fin (P.computeChipAt c).rap.w → F[X] :=
  fun j => Qc (Fin.cast (computeChipAt_width P c) j)

/-- Reindex a family compute trace at the honest-chip width. -/
def honestQc
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) :
    Fin P.computeChip.rap.w → F[X] :=
  fun j => Qc (Fin.cast (computeChipAt_width P c).symm j)

/-- Family-chip gather of `Qm` at tuple `c`.  Same trace polynomials as
`memoryBaseEnv`; `chalVal` is `memoryChalValOfTuple`. -/
def memoryBaseEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env F :=
  envOfTrace (P.memorySourceTrace Qm) P.optimized.orbit.ω
    (P.optimized.memoryNodes i)
    (memoryChalValOfTuple P.optimized.basis c) (P.familyMemoryPublic c)

/-- Family `𝕂` memory environment. -/
def memorySourceEnvAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env K :=
  gatherEnv P.optimized.basis ((memorySourceTemplate P.optimized.basis).col0 3)
    (memoryBaseEnvAt P c Qm i)

variable (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

theorem row_obligations_at (i : Fin (rows P)) :
    CorrectedComputeSourceObligations (rows P) (rowEnvAt P c Qc i)
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)) := by
  have h :=
    (productionNamedComputeRAP_satisfies_iff_sourceLanguage
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit Qc).1 hsat
  exact h.2 _ (by simp [rowNodeSet])

theorem packed_rowLocal_zero_at (i : Fin (rows P)) :
    ∀ g ∈ ComputePaperPacking.paperPackingRowLocal,
      g.eval (rowEnvAt P c Qc i).toSourceEnv = 0 :=
  paperPackingRowLocal_eval_zero (row_obligations_at P c Qc hsat i)

theorem packedTable_zero_at (i : Fin (rows P)) :
    ∀ g ∈ ComputePaperPacking.packedTableOptimized,
      g.eval (rowEnvAt P c Qc i).toSourceEnv = 0 :=
  fun g hg =>
    packed_rowLocal_zero_at P c Qc hsat i g (List.mem_append.mpr (Or.inl hg))

theorem alwaysOn_zero_at (i : Fin (rows P)) :
    ∀ g ∈ ComputePaperPacking.alwaysOnOptimized,
      g.eval (rowEnvAt P c Qc i).toSourceEnv = 0 :=
  fun g hg =>
    packed_rowLocal_zero_at P c Qc hsat i g (alwaysOn_mem_rowLocal hg)

theorem selector_gates_at_family (i : Fin (rows P)) :
    (∀ (k : ℕ) (hk : k < 11),
      (rowEnvAt P c Qc i).baseTrace ⟨k, by omega⟩ = 0 ∨
        (rowEnvAt P c Qc i).baseTrace ⟨k, by omega⟩ = 1) ∧
    ((rowEnvAt P c Qc i).baseTrace ⟨0, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨1, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨2, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨3, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨4, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨5, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨6, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨7, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨8, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨9, by norm_num⟩ +
      (rowEnvAt P c Qc i).baseTrace ⟨10, by norm_num⟩) = 1 := by
  have hb := (row_obligations_at P c Qc hsat i).base15
  set envF := envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c) with hE
  have hbase : ∀ k : ℕ, (hk : k < 13) →
      (rowEnvAt P c Qc i).baseTrace ⟨k, hk⟩ = envF.trace k :=
    fun _ _ => rfl
  constructor
  · intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    rw [hbase k (by omega)]
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    change envF.trace 0 + envF.trace 1 + envF.trace 2 + envF.trace 3 + envF.trace 4 +
      envF.trace 5 + envF.trace 6 + envF.trace 7 + envF.trace 8 + envF.trace 9 +
      envF.trace 10 = 1
    linear_combination hg

theorem rowSelector_oneHot_at
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin (rows P)) :
    ∃ s, rowSelector (rowEnvAt P c Qc i) = Nock.ComputeTable.opSel s := by
  obtain ⟨hbool, hsum⟩ := selector_gates_at_family P c Qc hsat i
  apply Nock.ComputeTable.oneHot_of_bool_sum _ hchar
  · intro st
    rcases hbool (Nock.Reified.opCol st) (by cases st <;> decide) with h | h
    · left; simp [rowSelector, h]
    · right; simp [rowSelector, h]
  · have hK := congrArg (algebraMap F K) hsum
    simp only [map_add, map_one] at hK
    simp only [rowSelector, Nock.ComputeTable.sum09, Nock.Reified.opCol]
    linear_combination hK

theorem deployed_row_one_hot_at (i : Fin (rows P)) :
    ∃ st : State, OneHotSelector (rowEnvAt P c Qc i).toSourceEnv st := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_at P c Qc hsat (pkgHchar P) i
  refine ⟨s, fun t => ?_⟩
  have ht : (rowEnvAt P c Qc i).toSourceEnv.trace (opCol t) = opSel s t := by
    rw [source_trace_base _ (opCol t) (by cases t <;> decide)]
    simpa [rowSelector] using congrFun hs t
  simpa [OneHotSelector, opSel] using ht

variable (hz : nprSeed c.1 ≠ 0)
include hz

/-- Every accepted row of `computeChipAt c` is
`V_comp` at the fingerprints `rowEnvAt` decodes. -/
theorem deployed_row_vcomp_at (i : Fin (rows P)) :
    VcompAt (rowEnvAt P c Qc i) := by
  obtain ⟨st, hone⟩ := deployed_row_one_hot_at P c Qc hsat i
  refine ⟨st, hone, ?_⟩
  set env := (rowEnvAt P c Qc i).toSourceEnv
  set E := decodeSource (rowEnvAt P c Qc i)
  have hzZ : (zZinvExpr.subst computeSubst).eval env = 0 :=
    zZinv_at_rowEnvAt P c Qc i hz
  have hpk := packedTable_zero_at P c Qc hsat i
  have hatomic :=
    (paperPacking_iff_atomic env st hone hzZ).1 hpk
  have hrefold : ∀ e ∈ refoldedPerStateGates, e.eval env = 0 := by
    intro e he
    have hsb : e ∈ stateBlocks := by
      simpa [stateBlocks_eq_refolded] using he
    simp only [stateBlocks, List.mem_flatten, List.mem_map] at hsb
    obtain ⟨_, ⟨s, -, rfl⟩, he'⟩ := hsb
    exact hatomic s e he'
  have hgated : ∀ e ∈ perStateGated, e.eval E = 0 :=
    (refolded_iff_perStateGated env st hone).1 hrefold
  have hsvBase := svBaseGates_of_oneHot (env := env) (st := st) hone
  have hon := alwaysOn_zero_at P c Qc hsat i
  have hsubst_id_sv : ∀ e ∈ svBaseGates, e.subst computeSubst = e := by
    intro e he
    simp only [svBaseGates, svBoolExprs, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨t, -, rfl⟩ | rfl
    · cases t <;> rfl
    · rfl
  have hsvE : ∀ e ∈ svExprs, e.eval E = 0 := by
    intro e he
    simp only [svExprs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with hbool | rfl | rfl | rfl | rfl
    · have hmem : e ∈ svBaseGates := List.mem_append.mpr (Or.inl hbool)
      rw [show e.eval E = (e.subst computeSubst).eval env from
        (Expr.eval_subst computeSubst e env).symm, hsubst_id_sv e hmem]
      exact hsvBase e hmem
    · have hmem : svOneHotExprF ∈ svBaseGates := by simp [svBaseGates]
      rw [show svOneHotExprF.eval E = (svOneHotExprF.subst computeSubst).eval env from
        (Expr.eval_subst computeSubst svOneHotExprF env).symm, hsubst_id_sv _ hmem]
      exact hsvBase _ hmem
    · have hmem : sv4Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv4Expr env).symm.trans (hon _ hmem)
    · have hmem : sv5Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv5Expr env).symm.trans (hon _ hmem)
    · have hmem : sv6Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv6Expr env).symm.trans (hon _ hmem)
  have hformE : ∀ e ∈ formulaExprs, e.eval E = 0 := by
    intro e he
    have hmem : e.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
      simp only [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized,
        List.mem_append, List.mem_cons, List.mem_map]
      exact Or.inr ⟨e, he, rfl⟩
    exact (Expr.eval_subst computeSubst e env).symm.trans (hon _ hmem)
  have hmr1E : ∀ e ∈ mr1Exprs, e.eval E = 0 := by
    intro e he
    exact (Expr.eval_subst computeSubst e env).symm.trans (mr1Exprs_subst_vanish env e he)
  have hzE : zZinvExpr.eval E = 0 :=
    (Expr.eval_subst computeSubst zZinvExpr env).symm.trans hzZ
  have hallE : ∀ cons ∈ computeAIR.constraints, cons.expr.eval E = 0 := by
    intro cons hc
    have hc' : cons ∈
        (svExprs.map (fun e => ⟨.row, e⟩) ++
          formulaExprs.map (fun e => ⟨.row, e⟩) ++
          mr1Exprs.map (fun e => ⟨.row, e⟩) ++
          [⟨.row, zZinvExpr⟩] ++
          perStateGated.map (fun e => ⟨.row, e⟩)) := hc
    rcases List.mem_append.mp hc' with hL | hD
    · rcases List.mem_append.mp hL with hL2 | hzmem
      · rcases List.mem_append.mp hL2 with hL3 | hC
        · rcases List.mem_append.mp hL3 with hA | hB
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hA; exact hsvE e he
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hB; exact hformE e he
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hC; exact hmr1E e he
      · simp only [List.mem_singleton] at hzmem; subst cons; exact hzE
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hD; exact hgated e he
  have hz93 : E.trace 93 = (E.chal 1)⁻¹ := trace93_eq_inv_of_zZinv E hzE
  have hop : opOf E = opSel st := by
    funext t
    have honeE : OneHotSelector E st := oneHot_ofSubst env st hone
    simpa [opOf, opSel] using honeE t
  have hre' : ∀ cons ∈ computeAIR.constraints,
      cons.expr.eval (computeEnvFull (inpOf E) (opSel (pubOfState E st).state)
        (pubOfState E st) (decOf E) (exOf E)) = 0 := by
    intro cons hc
    have hkind : cons.kind = .row := by
      have := List.all_eq_true.mp computeAIR_all_row cons hc
      simpa [beq_iff_eq] using this
    have hchained : cons ∈ Trans.computeAIRchained.constraints :=
      List.mem_append.mpr (Or.inl hc)
    have hagree := row_constraint_eval_agree E st hz93 cons hchained hkind
    have hopub : opSel (pubOfState E st).state = opOf E := by
      simpa [pubOfState] using hop.symm
    rw [hopub, ← hagree]
    exact hallE cons hc
  have hrap :=
    (computeAIR_sound (inp := inpOf E) (pub := pubOfState E st)
      (dec := decOf E) (ex := exOf E)).mp hre'
  exact equiv_compute_sound _ _ _ ⟨decodeEx (rowEnvAt P c Qc i), hrap.1⟩

end

end Nock.NockVMROM.Thm54.FamilyComputeRows
