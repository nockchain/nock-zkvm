/-
  Nock/NockVMROM/Thm54/WrapComputeConjuncts.lean

  Compute conjuncts through the wrap identity.
  `vcomp` is `deployed_row_vcomp_at` transported by
  `wrap_fixes_vcomp_row`.  `ln_chain` is the committed hand-off at the
  family chip.  `computeRows` is `computeRowAccepted_iff` =
  state agreement + `Vcomp`.
-/
import Nock.NockVMROM.Thm54.WrapFixesVcomp
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.ChainedLanguage
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.Framework.NockInstances
import Nock.NockVMROM.Thm54.ExprSubstitution
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.WrapComputeConjuncts

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.AcceptedContentOfTracesFill
open Nock.NockVMROM.Thm54.WrapFixesVcomp
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ExactExecution
open MonolithicRAP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem wrap_specialize_dec (row : State × DTcomp K) (α : K) :
    ((wrapComputeLabel row).specialize α).2.2.2 = row.2.2.2 := by
  simp [wrapComputeLabel, ComputeRowTemplate.specialize]

variable {F : Type} [Field F] [Algebra F K]

theorem subst_tc66 : Expr.subst computeSubst (tc 66) = lnCur .traceCur := by
  change computeTraceSubst .traceCur 66 = _
  norm_num [computeTraceSubst, lnCur, ext0]

noncomputable section

variable [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem decodePub_ln_prev (env : CorrectedFinalTypedEnv F K) (st : State) :
    (decodePub env st).ln_prev = lnPrevAt env := by
  simp [decodePub, pubOfState, decodeSource, Env.ofSubst]
  rw [show computeSubst .traceCur 65 = lnPrev .traceCur from subst_tc65]
  change env.toSourceEnv.trace 67 = _
  exact source_trace_lnPrev env

theorem decodePub_ln (env : CorrectedFinalTypedEnv F K) (st : State) :
    (decodePub env st).ln = lnCurAt env := by
  simp [decodePub, pubOfState, decodeSource, Env.ofSubst]
  rw [show computeSubst .traceCur 66 = lnCur .traceCur from subst_tc66]
  change env.toSourceEnv.trace 68 = _
  exact source_trace_lnCur env

/-- Family last-row mask (`baseTrace 12`), twin of `masks_at_row`. -/
theorem masks_last_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).baseTrace 12 =
      (if i = lastRow P then 1 else 0) := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
    (P.familyComputePublic c) P.optimized.orbit Qc).1 hsat).1
  have hinj := P.optimized.computeNodes_injective
  have h1 := hbind ⟨1, by change 1 < 2; norm_num⟩
  have h12 : 12 < (P.computeChipAt c).rap.w := by
    have hw := computeChipAt_width P c
    change 12 < 303
    norm_num
  have hc1 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis
      (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, by
          change 12 < 303; norm_num⟩ := rfl
  rw [hc1] at h1
  show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace 12 = _
  have h12' : 12 < (P.computeChipAt c).rap.w := h12
  simp only [envOfTrace, dif_pos h12']
  rw [show (Qc ⟨12, h12'⟩) = Nock.Framework.lastRowMask
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes from h1,
    Nock.Framework.lastRowMask_eval _ _ hinj]

/-- Family hand-off: off the last row, `ln(i) = ln_prev(i+1)`. -/
theorem ln_chain_at_family
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    lnCurAt (rowEnvAt P c Qc i) = lnPrevAt (rowEnvAt P c Qc ⟨(i : ℕ) + 1, hi⟩) := by
  have hnl : (rowEnvAt P c Qc i).baseTrace 12 = 0 := by
    rw [masks_last_at P c Qc hsat i, if_neg]
    intro heq
    have hv : (i : ℕ) = rows P - 1 := congrArg Fin.val heq
    omega
  rw [ln_chain (row_obligations_at P c Qc hsat i) hnl]
  have hadj := P.optimized.computeAdjacentOrbit i hi
  unfold lnPrevAt
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt : correctedFinalExtCoordIndex (e := 3) (54 : Fin 63) k <
      (P.computeChipAt c).rap.w := by
    change _ < 303
    simp [correctedFinalExtCoordIndex]
    omega
  simp only [envOfTrace, dif_pos hlt]
  rw [hadj]

/-- Specialized `Dec` is the decoded `Dec` (wrap does not touch it). -/
theorem specializedExec_computeDecAt_eq_decodeDec
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows) :
    ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeDecAt i =
      decodeDec
        (rowEnvAt P c (familyQc P c Qc)
          (Fin.cast
            ((specializedExec_compRows P Qc Qm c h hz).trans
              (cfgOfTraces_compRows P Qc Qm c)) i)) := by
  have hcfg := specializedExec_compRows P Qc Qm c h hz
  have hN := cfgOfTraces_compRows P Qc Qm c
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
  have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).compRows := by omega
  have hmap := specialized_computeRows_map P Qc Qm c h hz
  have hexec := execOfTraces_computeRows P Qc Qm c h
  have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).computeRows.length := by
    rw [(execOfTraces P Qc Qm c h).computeRows_length]; exact hi'
  have hget :
      (execOfTraces P Qc Qm c h).computeRows[(i : ℕ)]'hidxE =
        lblCAt P Qc c ⟨i.val, hi⟩ := by
    rw [List.getElem_of_eq hexec, List.getElem_map, List.getElem_range']
    simp [Nat.add_comm]
    exact lblC_succ P Qc c ⟨i.val, hi⟩
  have hidxS : (i : ℕ) <
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length := by
    rw [hmap, List.length_map]; exact hidxE
  have hrow :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows[(i : ℕ)]'hidxS =
        (wrapComputeLabel (lblCAt P Qc c ⟨i.val, hi⟩)).specialize (alphaM c.1) := by
    simp only [hmap]
    rw [List.getElem_map]
    exact congrArg (fun row => (wrapComputeLabel row).specialize (alphaM c.1)) hget
  have hdec :
      ((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeDecAt i =
        (((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows[(i : ℕ)]'hidxS).2.2.2 := by
    unfold ExactExecution.computeDecAt ExactExecution.computeRowAt
    rw [List.get_eq_getElem]
    congr 1
  have hcast :
      Fin.cast
        ((specializedExec_compRows P Qc Qm c h hz).trans
          (cfgOfTraces_compRows P Qc Qm c)) i =
        ⟨i.val, hi⟩ :=
    Fin.ext rfl
  rw [hdec, hrow, wrap_specialize_dec, hcast]
  simp [lblCAt]

/-- `vcomp` of `AcceptedContent` at the built strategy. -/
theorem specialized_vcomp
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows) :
    Vcomp
      ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).challenges.computeInputs
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt i)
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeDecAt i) := by
  have hcfg := specializedExec_compRows P Qc Qm c h hz
  have hN := cfgOfTraces_compRows P Qc Qm c
  have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
  have hv := deployed_row_vcomp_at P c (familyQc P c Qc) hsat hz ⟨i.val, hi⟩
  have hV := lblCAt_vcomp_of_vcompAt P Qc c ⟨i.val, hi⟩ hv
  have hpub :=
    specializedExec_computePubAt_eq_decodePub_of_accepted P Qc Qm c h hz hsat i
  have hdec :=
    specializedExec_computeDecAt_eq_decodeDec P Qc Qm c h hz i
  have hinp := specializedCfg_computeInputs P Qc Qm c h hz
  have hcast :
      Fin.cast (hcfg.trans hN) i = ⟨i.val, hi⟩ := Fin.ext rfl
  have hdi := decodeInputs_eq_specialized P Qc c ⟨i.val, hi⟩
  have hstLbl : (lblCAt P Qc c ⟨i.val, hi⟩).1 =
      computeStateOf (decodeSource (rowEnvAt P c (familyQc P c Qc) ⟨i.val, hi⟩)) :=
    rfl
  rw [hpub, hdec, hinp, hcast, hstLbl]
  simpa [hdi] using hV

/-- `ln_chain` of `AcceptedContent` at the built strategy. -/
theorem specialized_ln_chain
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows)
    (hi : (i : ℕ) + 1 <
        ((strategyOfTraces P Qc Qm c h).specializedCfg
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows) :
    (((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt i).ln =
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computePubAt
        ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  have hcfg := specializedExec_compRows P Qc Qm c h hz
  have hN := cfgOfTraces_compRows P Qc Qm c
  have hi0 : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
  have hi1 : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows := by omega
  have hpub0 :=
    specializedExec_computePubAt_eq_decodePub_of_accepted P Qc Qm c h hz hsat i
  have hpub1 :=
    specializedExec_computePubAt_eq_decodePub_of_accepted P Qc Qm c h hz hsat
      ⟨(i : ℕ) + 1, hi⟩
  have hcast0 : Fin.cast (hcfg.trans hN) i = ⟨i.val, hi0⟩ := Fin.ext rfl
  have hcast1 :
      Fin.cast (hcfg.trans hN) ⟨(i : ℕ) + 1, hi⟩ = ⟨(i : ℕ) + 1, hi1⟩ :=
    Fin.ext rfl
  rw [hpub0, hpub1, hcast0, hcast1, decodePub_ln, decodePub_ln_prev]
  exact ln_chain_at_family P c (familyQc P c Qc) hsat ⟨i.val, hi0⟩ hi1

/-- One specialized BFS row is `ComputeRowAccepted`. -/
theorem specialized_computeRowAccepted
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc))
    (i : Fin ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).compRows) :
    ComputeRowAccepted
      ((strategyOfTraces P Qc Qm c h).specializedCfg
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda)
      (((strategyOfTraces P Qc Qm c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRowAt i) := by
  refine (computeRowAccepted_iff _ _).2 ⟨?state, ?inp, ?v⟩
  · -- state agreement: wrap writes `pub.state := stamp.state`
    have hmap := specialized_computeRows_map P Qc Qm c h hz
    have hcfg := specializedExec_compRows P Qc Qm c h hz
    have hN := cfgOfTraces_compRows P Qc Qm c
    have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
    have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).compRows := by omega
    have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).computeRows.length := by
      rw [(execOfTraces P Qc Qm c h).computeRows_length]; exact hi'
    have hv := deployed_row_vcomp_at P c (familyQc P c Qc) hsat hz ⟨i.val, hi⟩
    have hV := lblCAt_vcomp_of_vcompAt P Qc c ⟨i.val, hi⟩ hv
    have hα : (lblCAt P Qc c ⟨i.val, hi⟩).2.1.α = alphaM c.1 := by
      have := decodeInputs_eq_specialized P Qc c ⟨i.val, hi⟩
      simpa [lblCAt] using congrArg Inputs.α this
    have hst : (lblCAt P Qc c ⟨i.val, hi⟩).1 =
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1.state := by
      simp [lblCAt, decodePub, pubOfState]
    have hfix :=
      wrap_fixes_vcomp_row
        (lblCAt P Qc c ⟨i.val, hi⟩).1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.2
        (alphaM c.1) hα hst (by simpa [lblCAt] using hV)
    have hexec := execOfTraces_computeRows P Qc Qm c h
    have hget :
        (execOfTraces P Qc Qm c h).computeRows[(i : ℕ)]'hidxE =
          lblCAt P Qc c ⟨i.val, hi⟩ := by
      rw [List.getElem_of_eq hexec, List.getElem_map, List.getElem_range']
      simp [Nat.add_comm]
      exact lblC_succ P Qc c ⟨i.val, hi⟩
    have hidxS : (i : ℕ) <
        ((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length := by
      rw [hmap, List.length_map]; exact hidxE
    have hrow :
        ((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRowAt i =
          (wrapComputeLabel (lblCAt P Qc c ⟨i.val, hi⟩)).specialize (alphaM c.1) := by
      unfold ExactExecution.computeRowAt
      have hidx : (i : ℕ) <
          ((strategyOfTraces P Qc Qm c h).specializedExec
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length := hidxS
      rw [List.get_eq_getElem]
      simp only [hmap]
      rw [List.getElem_map]
      exact congrArg (fun row => (wrapComputeLabel row).specialize (alphaM c.1)) hget
    rw [hrow, hfix]
    exact hst
  · have hinp := specializedCfg_computeInputs P Qc Qm c h hz
    have hcfg := specializedExec_compRows P Qc Qm c h hz
    have hN := cfgOfTraces_compRows P Qc Qm c
    have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
    -- inputs of the specialized row = decodeInputs = specializedCfg coins
    have hmap := specialized_computeRows_map P Qc Qm c h hz
    have hv := deployed_row_vcomp_at P c (familyQc P c Qc) hsat hz ⟨i.val, hi⟩
    have hV := lblCAt_vcomp_of_vcompAt P Qc c ⟨i.val, hi⟩ hv
    have hα : (lblCAt P Qc c ⟨i.val, hi⟩).2.1.α = alphaM c.1 := by
      have := decodeInputs_eq_specialized P Qc c ⟨i.val, hi⟩
      simpa [lblCAt] using congrArg Inputs.α this
    have hst : (lblCAt P Qc c ⟨i.val, hi⟩).1 =
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1.state := by
      simp [lblCAt, decodePub, pubOfState]
    have hfix :=
      wrap_fixes_vcomp_row
        (lblCAt P Qc c ⟨i.val, hi⟩).1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.2
        (alphaM c.1) hα hst (by simpa [lblCAt] using hV)
    have hexec := execOfTraces_computeRows P Qc Qm c h
    have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).compRows := by omega
    have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).computeRows.length := by
      rw [(execOfTraces P Qc Qm c h).computeRows_length]; exact hi'
    have hget :
        (execOfTraces P Qc Qm c h).computeRows[(i : ℕ)]'hidxE =
          lblCAt P Qc c ⟨i.val, hi⟩ := by
      rw [List.getElem_of_eq hexec, List.getElem_map, List.getElem_range']
      simp [Nat.add_comm]
      exact lblC_succ P Qc c ⟨i.val, hi⟩
    have hrow :
        ((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRowAt i =
          (wrapComputeLabel (lblCAt P Qc c ⟨i.val, hi⟩)).specialize (alphaM c.1) := by
      unfold ExactExecution.computeRowAt
      have hidxS : (i : ℕ) <
          ((strategyOfTraces P Qc Qm c h).specializedExec
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length := by
        rw [hmap, List.length_map]; exact hidxE
      rw [List.get_eq_getElem]
      simp only [hmap]
      rw [List.getElem_map]
      exact congrArg (fun row => (wrapComputeLabel row).specialize (alphaM c.1)) hget
    rw [hrow, hfix]
    have hdi := decodeInputs_eq_specialized P Qc c ⟨i.val, hi⟩
    simpa [lblCAt, hinp] using hdi
  · have hcfg := specializedExec_compRows P Qc Qm c h hz
    have hN := cfgOfTraces_compRows P Qc Qm c
    have hi : (i : ℕ) < P.optimized.family.problem.cfg.compRows := by omega
    have hmap := specialized_computeRows_map P Qc Qm c h hz
    have hexec := execOfTraces_computeRows P Qc Qm c h
    have hi' : (i : ℕ) < (cfgOfTraces P Qc Qm c).compRows := by omega
    have hidxE : (i : ℕ) < (execOfTraces P Qc Qm c h).computeRows.length := by
      rw [(execOfTraces P Qc Qm c h).computeRows_length]; exact hi'
    have hget :
        (execOfTraces P Qc Qm c h).computeRows[(i : ℕ)]'hidxE =
          lblCAt P Qc c ⟨i.val, hi⟩ := by
      rw [List.getElem_of_eq hexec, List.getElem_map, List.getElem_range']
      simp [Nat.add_comm]
      exact lblC_succ P Qc c ⟨i.val, hi⟩
    have hrow :
        ((strategyOfTraces P Qc Qm c h).specializedExec
            (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRowAt i =
          (wrapComputeLabel (lblCAt P Qc c ⟨i.val, hi⟩)).specialize (alphaM c.1) := by
      unfold ExactExecution.computeRowAt
      have hidxS : (i : ℕ) <
          ((strategyOfTraces P Qc Qm c h).specializedExec
              (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeRows.length := by
        rw [hmap, List.length_map]; exact hidxE
      rw [List.get_eq_getElem]
      simp only [hmap]
      rw [List.getElem_map]
      exact congrArg (fun row => (wrapComputeLabel row).specialize (alphaM c.1)) hget
    have hα : (lblCAt P Qc c ⟨i.val, hi⟩).2.1.α = alphaM c.1 := by
      have := decodeInputs_eq_specialized P Qc c ⟨i.val, hi⟩
      simpa [lblCAt] using congrArg Inputs.α this
    have hst : (lblCAt P Qc c ⟨i.val, hi⟩).1 =
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1.state := by
      simp [lblCAt, decodePub, pubOfState]
    have hV :=
      lblCAt_vcomp_of_vcompAt P Qc c ⟨i.val, hi⟩
        (deployed_row_vcomp_at P c (familyQc P c Qc) hsat hz ⟨i.val, hi⟩)
    have hfix :=
      wrap_fixes_vcomp_row
        (lblCAt P Qc c ⟨i.val, hi⟩).1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.1
        (lblCAt P Qc c ⟨i.val, hi⟩).2.2.2
        (alphaM c.1) hα hst (by simpa [lblCAt] using hV)
    rw [hrow, hfix]
    simpa [lblCAt] using hV

/-- `computeRows` of `AcceptedContent` at the built strategy. -/
theorem specialized_computeRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0)
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc)) :
    ((strategyOfTraces P Qc Qm c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).ComputeRowsAccepted := by
  rw [computeRowsAccepted_iff,
    ExactExecution.computeRows_eq_ofFn_computeRowAt]
  intro row hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact specialized_computeRowAccepted P Qc Qm c h hz hsat i

end

end Nock.NockVMROM.Thm54.WrapComputeConjuncts
