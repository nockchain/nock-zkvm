import Nock.NockVMROM.Thm54.VclL.Compute.FormulaLookup

/-!
# R-V4D1 / V4c item 1: the VCL obligations and the row decode — chip acceptance ⇒ `V_comp`

* `pullEnv` — the 309-shaped environment of a VCL row: column `i` of the 309 layout is VCL column
  `vclCol i` (`ChipVCL.lean`); since every kept 309 gate reads only `NoFormR` columns,
  `keptGates309_of_vclGates` transports acceptance (`eval_reindexE`).
* **`VclSourceObligations`** — the VCL source language: the 309 decomposition
  (`SourceObligations309`) minus Form R (`formR99`, `formRLam`, core ids `79`/`80`) and minus the
  arity-form exponent gates (the VCL serial is arity 1), i.e. base, the 80 kept core ids, the
  three aux positions, both endpoint lists and the endpoint equality checks.
  `VclSourceObligations.of_vclGates`: acceptance of `vclGates` at a row gives it at the gathered
  pull-back.
* `vcompAt_of_rowLocal` — the deployed `deployed_row_vcomp_at` argument with its package removed:
  the 72 row-local packed gates, a one-hot selector and the `z·z⁻¹` pin give `VcompAt`.
* **`vcl_row_vcomp`** — every row of an accepted VCL trace is `V_comp` at the fingerprints it
  decodes (premises: `hchar` as at the deployed chip and the `z·z⁻¹` pin of the row's challenge
  map — coin positions stay parametric, R-LC6).
* **`computeChipVCLD_row_vcomp`** and **`computeChipVCLD_lookup_binds_head`** — at the repaired
  chip: acceptance ⇒ `V_comp`, and with the slot-0 record served as the formula cell `[l r]`, the
  head is the row's opcode atom and `f_t` is the formula's axis-3 child.  This closes
  `lookup_binds_head_row`'s `V_comp` premise at the chip.

Paper: the paper (`V_comp`), `:1893-1898`, `:1850-1852`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.ComputeTable
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.MonolithicRAP
open Module

set_option maxRecDepth 300000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. The pull-back and the transport of acceptance -/

/-- The 309-shaped environment of a VCL row (column `i` ↦ VCL column `vclCol i`). -/
def pullEnv {F : Type*} (envV : Env F) : Env F where
  trace := fun i => envV.trace (vclCol i)
  traceNext := fun i => envV.traceNext (vclCol i)
  chal := envV.chal
  pub := envV.pub

theorem pullEnv_trace_lt {F : Type*} (envV : Env F) (i : ℕ) (hi : i < 202) :
    (pullEnv envV).trace i = envV.trace i := by
  simp [pullEnv, vclCol, hi]

section transport
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- **Acceptance transports**: the `vclGates` at a VCL row give every kept 309 gate at the
pull-back. -/
theorem keptGates309_of_vclGates (n : ℕ) (b : Basis (Fin 3) F K) (envV : Env F)
    (h : ∀ g ∈ vclGates n b, g.eval envV = 0) :
    ∀ g ∈ keptGates309 n b, g.eval (pullEnv envV) = 0 := by
  intro g hg
  have hr := h (reindexE g) (by simp only [vclGates, List.mem_append, List.mem_map]; exact Or.inl ⟨g, hg, rfl⟩)
  rwa [eval_reindexE g (pullEnv envV) envV (keptGates309_colsIn n b g hg)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl] at hr

end transport

/-! ## 2. The VCL source language -/

section obligations
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- **The VCL source obligations** of one row (the 309 decomposition minus Form R and the
arity-form exponent gates). -/
structure VclSourceObligations (n : ℕ) (env : Env309 F K) (envF : Env F) : Prop where
  base15 : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0
  extensionCore : ∀ i ∈ keptCoreIds, coreSemValue309 env i = 0
  residualAux : ∀ j : CorrectedResidualWitnessId, auxSemValue309 env j = 0
  endpointDegreeTwo : ∀ t ∈ endpoint2_309, t.eval env = 0
  endpointDegreeFour : ∀ t ∈ endpoint4_309, t.eval env = 0
  selectorEquality2 : ∀ g ∈ finalEndpointEqualityChecks, g.eval envF = 0

/-- The 309 obligations restrict to the VCL ones (positive control: the VCL language is no
stronger than the 309 one). -/
theorem VclSourceObligations.of309 {n : ℕ} {env : Env309 F K} {envF : Env F}
    (h : SourceObligations309 n env envF) : VclSourceObligations n env envF :=
  ⟨h.base15, fun i _ => h.extensionCore i, h.residualAux, h.endpointDegreeTwo,
    h.endpointDegreeFour, h.selectorEquality2⟩

variable [FiniteDimensional F K]

/-- **The kept 309 gates at a 309-shaped row give the VCL obligations at its gather.** -/
theorem VclSourceObligations.of_kept (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F)
    (h : ∀ g ∈ keptGates309 n b, g.eval envF = 0) :
    VclSourceObligations n (gather309 b envF) envF := by
  have henv := isCoordEnv309_gather b envF
  simp only [keptGates309, List.forall_mem_append] at h
  obtain ⟨⟨⟨⟨⟨hb, hc⟩, ha⟩, h2⟩, h4⟩, heq⟩ := h
  refine ⟨hb, ?_, (aux309_eval_iff b _ envF henv).1 ha,
    (compileList309_eval_iff b _ envF henv endpoint2_309).1 h2,
    (compileList309_eval_iff b _ envF henv endpoint4_309).1 h4, heq⟩
  intro i hi
  rw [eq_iff_coords_eq b (coreSemValue309 _ i) 0]
  intro k
  rw [coord_zero' b k, ← coreCoord309_eval b _ envF henv i k]
  apply hc
  simp only [correctedCoreVCL, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨i, hi, rfl⟩, List.mem_ofFn.mpr ⟨k, rfl⟩⟩

/-- **Acceptance of `vclGates` at a VCL row gives the VCL obligations** at the gathered pull-back. -/
theorem VclSourceObligations.of_vclGates (n : ℕ) (b : Basis (Fin 3) F K) (envV : Env F)
    (h : ∀ g ∈ vclGates n b, g.eval envV = 0) :
    VclSourceObligations n (gather309 b (pullEnv envV)) (pullEnv envV) :=
  VclSourceObligations.of_kept n b _ (keptGates309_of_vclGates n b envV h)

end obligations

/-! ## 3. The row-local readers and `V_comp` -/

section vcomp
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The 72 row-local packed gates vanish on a row with the VCL obligations (no core id `< 72` is a
Form R id or a retargeted queue position). -/
theorem paperPackingRowLocal_eval_zero_vcl {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligations n env envF) :
    ∀ g ∈ OptimizedComputeGateBasis.paperPackingRowLocal, g.eval env.base.toSourceEnv = 0 := by
  intro g hg
  obtain ⟨k, hget⟩ := List.mem_iff_get.mp hg
  have hk : (k : ℕ) < 72 := by
    have := k.isLt
    simpa [OptimizedComputeGateBasis.paperPackingRowLocal_length] using this
  have hkept : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ∈ keptCoreIds := by
    simp only [keptCoreIds, List.mem_filter, List.mem_finRange, true_and, formRCoreIds]
    simp; omega
  have hc := hsource.extensionCore _ hkept
  have hq1 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedQueueNonEmptyId := by
    intro h; have := congrArg Fin.val h; simp [packedQueueNonEmptyId] at this; omega
  have hq2 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedQueueTilingId := by
    intro h; have := congrArg Fin.val h; simp [packedQueueTilingId] at this; omega
  have h75 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedWalkCountId := by
    intro h; have := congrArg Fin.val h; simp [packedWalkCountId] at this; omega
  have h76 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedWalkAccId := by
    intro h; have := congrArg Fin.val h; simp [packedWalkAccId] at this; omega
  have h80 : (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) ≠ packedChainId := by
    intro h; have := congrArg Fin.val h; simp [packedChainId] at this; omega
  have h89 : ¬ ((⟨k.val, by omega⟩ : CorrectedCoreExtGateId) = packedLnChainId ∨
      (⟨k.val, by omega⟩ : CorrectedCoreExtGateId) = packedWalkLnId) := by
    rintro (h | h)
    · have := congrArg Fin.val h; simp [packedLnChainId] at this; omega
    · have := congrArg Fin.val h; simp [packedWalkLnId] at this; omega
  have hgate : (correctedFinalExtGate ⟨k.val, by omega⟩).eval env.base = 0 := by
    simp only [coreSemValue309, hq1, hq2, ↓reduceIte] at hc
    have h7 : ¬ ((k : ℕ) = 72 ∨ (k : ℕ) = 73) := by omega
    simpa [correctedCoreSemanticValue, h75, h76, h80, h89, h7] using hc
  have hlen : (k : ℕ) < OptimizedComputeGateBasis.finalExtTransitionGates.length := by simp; omega
  have hsrc := (correctedFinalExtGate_eval_source env.base ⟨k.val, by omega⟩).trans hgate
  have hget' : OptimizedComputeGateBasis.finalExtTransitionGates.get ⟨k.val, hlen⟩ = OptimizedComputeGateBasis.paperPackingRowLocal.get k := by
    have hk' : k.val < OptimizedComputeGateBasis.paperPackingRowLocal.length := k.isLt
    have hdecomp : OptimizedComputeGateBasis.finalExtTransitionGates =
        OptimizedComputeGateBasis.paperPackingRowLocal ++ (OptimizedComputeGateBasis.crossRowSingletons ++
          OptimizedComputeGateBasis.queueWitnessGates ++ OptimizedComputeGateBasis.finalSampledIOTransitionGates) := by
      rw [OptimizedComputeGateBasis.finalExtTransitionGates, OptimizedComputeGateBasis.paperPacking_eq_rowLocal_append]
      simp [List.append_assoc]
    have hq : OptimizedComputeGateBasis.finalExtTransitionGates[k.val]? = OptimizedComputeGateBasis.paperPackingRowLocal[k.val]? := by
      rw [hdecomp]
      exact List.getElem?_append_left hk'
    apply Option.some_inj.mp
    simpa [List.get_eq_getElem] using
      (List.getElem?_eq_getElem hlen).symm.trans (hq.trans (List.getElem?_eq_getElem hk'))
  rw [← hget, ← hget']
  exact hsrc

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- **`V_comp` from the row-local language** (the argument of `deployed_row_vcomp_at`, package-free):
the 72 row-local packed gates, a one-hot selector and the `z·z⁻¹` pin give `VcompAt`. -/
theorem vcompAt_of_rowLocal (env : CorrectedFinalTypedEnv F K) (st : State)
    (hone : OneHotSelector env.toSourceEnv st)
    (hzZ : (zZinvExpr.subst computeSubst).eval env.toSourceEnv = 0)
    (hpk : ∀ g ∈ OptimizedComputeGateBasis.paperPackingRowLocal, g.eval env.toSourceEnv = 0) :
    VcompAt env := by
  refine ⟨st, hone, ?_⟩
  set envS := env.toSourceEnv
  set E := decodeSource env
  have hpkT : ∀ g ∈ ComputePaperPacking.packedTableOptimized, g.eval envS = 0 :=
    fun g hg => hpk g (List.mem_append.mpr (Or.inl hg))
  have hon : ∀ g ∈ ComputePaperPacking.alwaysOnOptimized, g.eval envS = 0 :=
    fun g hg => hpk g (alwaysOn_mem_rowLocal hg)
  have hatomic := (paperPacking_iff_atomic envS st hone hzZ).1 hpkT
  have hrefold : ∀ e ∈ refoldedPerStateGates, e.eval envS = 0 := by
    intro e he
    have hsb : e ∈ stateBlocks := by
      simpa [stateBlocks_eq_refolded] using he
    simp only [stateBlocks, List.mem_flatten, List.mem_map] at hsb
    obtain ⟨_, ⟨s, -, rfl⟩, he'⟩ := hsb
    exact hatomic s e he'
  have hgated : ∀ e ∈ perStateGated, e.eval E = 0 :=
    (refolded_iff_perStateGated envS st hone).1 hrefold
  have hsvBase := svBaseGates_of_oneHot (env := envS) (st := st) hone
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
      rw [show e.eval E = (e.subst computeSubst).eval envS from
        (Expr.eval_subst computeSubst e envS).symm, hsubst_id_sv e hmem]
      exact hsvBase e hmem
    · have hmem : svOneHotExprF ∈ svBaseGates := by simp [svBaseGates]
      rw [show svOneHotExprF.eval E = (svOneHotExprF.subst computeSubst).eval envS from
        (Expr.eval_subst computeSubst svOneHotExprF envS).symm, hsubst_id_sv _ hmem]
      exact hsvBase _ hmem
    · have hmem : sv4Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv4Expr envS).symm.trans (hon _ hmem)
    · have hmem : sv5Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv5Expr envS).symm.trans (hon _ hmem)
    · have hmem : sv6Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv6Expr envS).symm.trans (hon _ hmem)
  have hformE : ∀ e ∈ formulaExprs, e.eval E = 0 := by
    intro e he
    have hmem : e.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
      simp only [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized,
        List.mem_append, List.mem_cons, List.mem_map]
      exact Or.inr ⟨e, he, rfl⟩
    exact (Expr.eval_subst computeSubst e envS).symm.trans (hon _ hmem)
  have hmr1E : ∀ e ∈ mr1Exprs, e.eval E = 0 := by
    intro e he
    exact (Expr.eval_subst computeSubst e envS).symm.trans (mr1Exprs_subst_vanish envS e he)
  have hzE : zZinvExpr.eval E = 0 :=
    (Expr.eval_subst computeSubst zZinvExpr envS).symm.trans hzZ
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
    have honeE : OneHotSelector E st := oneHot_ofSubst envS st hone
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
  exact equiv_compute_sound _ _ _ ⟨decodeEx env, hrap.1⟩

/-- **The one-hot selector from the base gates** of a gathered row (`hchar` as at the deployed
chip). -/
theorem oneHot_of_base15 [FiniteDimensional F K] (n : ℕ) (b : Basis (Fin 3) F K) (envF : Env F)
    (hb : ∀ g ∈ finalBaseTransitionGates n, g.eval envF = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1) :
    ∃ st : State, OneHotSelector (gatherCorrectedFinalTypedEnv b envF).toSourceEnv st := by
  set env := gatherCorrectedFinalTypedEnv b envF
  have hbase : ∀ k : ℕ, (hk : k < 13) → env.baseTrace ⟨k, hk⟩ = envF.trace k := fun _ _ => rfl
  have hbool : ∀ (k : ℕ) (hk : k < 11),
      env.baseTrace ⟨k, by omega⟩ = 0 ∨ env.baseTrace ⟨k, by omega⟩ = 1 := by
    intro k hk
    have hg := hb (selectorBool k) (by
      simp only [finalBaseTransitionGates, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨k, hk, rfl⟩)
    rw [hbase k (by omega)]
    simp only [selectorBool, bv, CoeffExpr.eval, mul_eq_zero, sub_eq_zero] at hg
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have hsum : env.baseTrace ⟨0, by norm_num⟩ + env.baseTrace ⟨1, by norm_num⟩ +
      env.baseTrace ⟨2, by norm_num⟩ + env.baseTrace ⟨3, by norm_num⟩ +
      env.baseTrace ⟨4, by norm_num⟩ + env.baseTrace ⟨5, by norm_num⟩ +
      env.baseTrace ⟨6, by norm_num⟩ + env.baseTrace ⟨7, by norm_num⟩ +
      env.baseTrace ⟨8, by norm_num⟩ + env.baseTrace ⟨9, by norm_num⟩ +
      env.baseTrace ⟨10, by norm_num⟩ = 1 := by
    have hg := hb selectorOneHot (by simp [finalBaseTransitionGates])
    simp [selectorOneHot, selectorSum, CoeffExpr.sumList, List.range_succ, bv, CoeffExpr.eval,
      sub_eq_zero] at hg
    change envF.trace 0 + envF.trace 1 + envF.trace 2 + envF.trace 3 + envF.trace 4 +
      envF.trace 5 + envF.trace 6 + envF.trace 7 + envF.trace 8 + envF.trace 9 +
      envF.trace 10 = 1
    linear_combination hg
  obtain ⟨s, hs⟩ : ∃ s, rowSelector env = Nock.ComputeTable.opSel s := by
    apply Nock.ComputeTable.oneHot_of_bool_sum _ hchar
    · intro st
      rcases hbool (Nock.Reified.opCol st) (by cases st <;> decide) with h | h
      · left; simp [rowSelector, h]
      · right; simp [rowSelector, h]
    · have hK := congrArg (algebraMap F K) hsum
      simp only [map_add, map_one] at hK
      simp only [rowSelector, Nock.ComputeTable.sum09, Nock.Reified.opCol]
      linear_combination hK
  refine ⟨s, fun t => ?_⟩
  have ht : env.toSourceEnv.trace (opCol t) = opSel s t := by
    rw [source_trace_base _ (opCol t) (by cases t <;> decide)]
    simpa [rowSelector] using congrFun hs t
  simpa [OneHotSelector, opSel] using ht

/-- **Every row with the VCL obligations is `V_comp`** at the fingerprints it decodes. -/
theorem vcl_obligations_vcomp [FiniteDimensional F K] (n : ℕ) (b : Basis (Fin 3) F K)
    (envF : Env F) (h : VclSourceObligations n (gather309 b envF) envF)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hzZ : (zZinvExpr.subst computeSubst).eval
      (gatherCorrectedFinalTypedEnv b envF).toSourceEnv = 0) :
    VcompAt (gatherCorrectedFinalTypedEnv b envF) := by
  obtain ⟨st, hone⟩ := oneHot_of_base15 n b envF h.base15 hchar
  exact vcompAt_of_rowLocal _ st hone hzZ (paperPackingRowLocal_eval_zero_vcl h)

/-- **`vcl_row_vcomp`: a row accepted by `vclGates` is `V_comp`.** -/
theorem vcl_row_vcomp [FiniteDimensional F K] (n : ℕ) (b : Basis (Fin 3) F K) (envV : Env F)
    (h : ∀ g ∈ vclGates n b, g.eval envV = 0)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (hzZ : (zZinvExpr.subst computeSubst).eval
      (gatherCorrectedFinalTypedEnv b (pullEnv envV)).toSourceEnv = 0) :
    VcompAt (gatherCorrectedFinalTypedEnv b (pullEnv envV)) :=
  vcl_obligations_vcomp n b _ (VclSourceObligations.of_vclGates n b envV h) hchar hzZ

end vcomp

/-! ## 4. At the repaired chip -/

section chip
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The decoded fingerprints of the pull-back are the VCL row's own (roles `< 63` read columns
`< 202`, where `vclCol` is the identity): the slot-0 record's `f_h` / `f_t` ARE the decoded ones. -/
theorem fpAt_pullEnv (b : Basis (Fin 3) F K) (envV : Env F) (R : ℕ) (hR : R + 2 < 63) :
    fpAt b (pullEnv envV) R = fpAt b envV R := by
  have h : ∀ j : Fin 3, ∀ k : Fin 3,
      (pullEnv envV).trace (roleLimb (R + (j : ℕ)) + (k : ℕ)) =
        envV.trace (roleLimb (R + (j : ℕ)) + (k : ℕ)) := by
    intro j k
    apply pullEnv_trace_lt
    have := j.isLt; have := k.isLt; simp only [roleLimb]; omega
  simp only [fpAt, fpEntry, Entry.val, h]

/-- **At `computeChipVCLD`: acceptance ⇒ `V_comp`** at every row node. -/
theorem computeChipVCLD_row_vcomp {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit) P)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hzZ : (zZinvExpr.subst computeSubst).eval (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv = 0) :
    VcompAt (gatherCorrectedFinalTypedEnv b (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))) := by
  have hall := ((computeChipVCLD_sat_iff hn nodes b γc ρc chalV pubVal orbit P).1 hP).2 x hx
  refine vcl_row_vcomp n b _ (fun g hg => hall g ?_) hchar hzZ
  simp only [vclGatesD, vclGatesA, List.mem_append]
  exact Or.inl (Or.inl hg)

/-- **`lookup_binds_head` at the chip**: on an accepted row of `computeChipVCLD` in state
`st ≠ cons`, if the slot-0 record's fingerprints `(f, f_h, f_t)` are served as the formula cell
`[l r]` (the export lookup's provider, frame side), then `l` is the opcode atom and the row's
`f_t` is the formula's axis-3 child. -/
theorem computeChipVCLD_lookup_binds_head {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X])
    (hP : RAP.SatisfiesWithPreprocessing (computeChipVCLD hn nodes b γc ρc chalV pubVal orbit) P)
    (hchar : ∀ m : ℕ, m ≤ 11 → (m : K) = 1 → m = 1)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (hzZ : (zZinvExpr.subst computeSubst).eval (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv = 0)
    (st : State)
    (hone : OneHotSelector (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))).toSourceEnv st)
    (hcons : st ≠ State.cons) (W : ℕ)
    (hz : (decodeInputs (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z ≠ 0)
    (hwin : ∀ k, 0 < k → k < W → (decodeInputs (gatherCorrectedFinalTypedEnv b
      (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z ^ k ≠ 1)
    (hop : st.toNat < ringChar K) {l r : Noun} (hW : l.leaves ≤ W)
    (hl : ∀ a, l = .atom a → a < ringChar K)
    (hsv : ServedFormulaCell (decodeInputs (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z
      (decodePub (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal))) st)
      (decodeDec (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))) l r) :
    l = .atom st.toNat ∧ Noun.slot 3 (.cell l r) = some r ∧
      Nock.GlobalCarryRecognizer.enc (decodeInputs (gatherCorrectedFinalTypedEnv b
        (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).z r =
        (decodeDec (gatherCorrectedFinalTypedEnv b
          (pullEnv (Reify.envOfTrace P orbit.ω x chalV pubVal)))).f_t := by
  obtain ⟨st', hone', hV⟩ := computeChipVCLD_row_vcomp hn nodes b γc ρc chalV pubVal orbit P hP
    hchar x hx hzZ
  have hst : st' = st := by
    by_contra hne
    have a := hone' st
    have c := hone st
    simp only [if_neg (Ne.symm hne)] at a c
    rw [a] at c
    exact zero_ne_one c
  subst hst
  exact lookup_binds_head_row hV hcons hz W hwin hop hW hl hsv

end chip

end

end VclL.Compute
end Nock.NockVMROM.Thm54
