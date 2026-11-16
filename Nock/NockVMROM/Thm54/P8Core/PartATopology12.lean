/-
  Nock/NockVMROM/Thm54/P8Core/PartATopology12.lean

  The topology bad-`γ` set at `(z, αM, λ)` (`specializedTopologyFailureEvent`) reads the specialized
  compute tree and the specialized memory forest of the event template `execTemplateEv`.  We show
  it is a function of the B0 ∪ B1 columns of the two committed traces:

  * the event template's COMPUTE tree is literally the same tree (`execTemplateEv_computeTree_B01`):
    every decoded label column `0..92` and the five decoded inputs read source columns of round
    `≤ 1` only (`labReads_round_le`, `chReads_round_le`, decided);
  * the event template's MEMORY forest agrees after the projection `projM` onto
    `(state, pt, lc, rc)`, the only label fields the memory topology payloads read
    (`execTemplateEv_memoryForest_B01`): state from memory base `0..2`, `pt`/`lc`/`rc` from memory
    `𝕂`-roles `0..14`, all round `≤ 1`;
  * `topologyBadGammas_congr_proj` turns those two facts into equality of the bad set
    (`topoBad_B01`).

  The coins it reads directly are `z`, `αM`, `λ` (all M1).  Scope: the repartitioned schedule and the
  parallel package only
-/
import Nock.NockVMROM.Thm54.P8Core.PartASummandsM2
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.PartAStaged

open scoped Polynomial
open Nock Nock.Reified Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.ReconTreeSize
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.PartA12

noncomputable section

/-! ## 0. Decided read sets of the compute label decoder -/

/-- Every source read of the decoded label columns `0..92`. -/
def labReads : List (VarKind × ℕ) :=
  (List.range 93).flatMap fun k => Unhosted309.readsE (computeSubst .traceCur k)

/-- Every source read of the decoded inputs (challenges `0..4`). -/
def chReads : List (VarKind × ℕ) :=
  (List.range 5).flatMap fun k => Unhosted309.readsE (computeSubst .challenge k)

theorem labReads_round_le :
    ∀ q ∈ labReads, (q.1 = .traceCur ∨ q.1 = .traceNext) → srcRoundW q.2 ≤ 1 := by decide +kernel

theorem chReads_round_le :
    ∀ q ∈ chReads, (q.1 = .traceCur ∨ q.1 = .traceNext) → srcRoundW q.2 ≤ 1 := by decide +kernel

/-! ## 1. The label decoders read the decoded columns `0..92` and challenges `0..4` -/

section Decode
variable {K : Type} [Field K] [DecidableEq K]

/-- The decoded environment cut to what the compute label reads. -/
def dTrunc (D : Env K) : Env K :=
  ⟨fun k => if k < 93 then D.trace k else 0, fun _ => 0,
    fun k => if k < 5 then D.chal k else 0, fun _ => 0⟩

theorem computeStateOf_dTrunc (D : Env K) :
    StrategyOfTracesLift.computeStateOf D = StrategyOfTracesLift.computeStateOf (dTrunc D) := by
  unfold StrategyOfTracesLift.computeStateOf dTrunc
  simp

theorem inpOf_dTrunc (D : Env K) : inpOf D = inpOf (dTrunc D) := by
  simp [inpOf, dTrunc]

theorem pubOfState_dTrunc (D : Env K) (st : State) : pubOfState D st = pubOfState (dTrunc D) st := by
  simp [pubOfState, fpOf, mrOf, dTrunc]

theorem decOf_dTrunc (D : Env K) : decOf D = decOf (dTrunc D) := by
  simp [decOf, fpOf, dTrunc]

end Decode

/-! ## 2. The projection-level topology congruence -/

section Proj
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- The memory label projection onto what the memory topology payloads read. -/
def projM (d : MState × DTmem K) (l : MState × DTmem K) : MState × DTmem K :=
  (l.1, (d.2.1, { d.2.2 with pt := l.2.2.pt, lc := l.2.2.lc, rc := l.2.2.rc }))

/-- **The topology bad-`γ` set reads the compute tree and the `projM`-image of the memory
forest.** -/
theorem topologyBadGammas_congr_proj (R R' : RawPlusIOSegmentedFamily F K) (d : MState × DTmem K)
    (hC : R.exec.computeTree = R'.exec.computeTree)
    (hM : R.exec.memoryForest.map (mapNTree (projM d)) =
      R'.exec.memoryForest.map (mapNTree (projM d))) :
    topologyBadGammas R = topologyBadGammas R' := by
  have key : ∀ (t : NTree (MState × DTmem K)) (i : Fin 2),
      memorySlotBadGammas (mapNTree (projM d) t) i = memorySlotBadGammas t i :=
    fun t i => P8EventEv.memorySlotBadGammas_mapNTree (projM d) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) t i
  have hrowsM : R.memoryWalkRows.map (mapNTree (projM d)) =
      R'.memoryWalkRows.map (mapNTree (projM d)) := by
    show (bfsForest R.exec.memoryForest).map _ = (bfsForest R'.exec.memoryForest).map _
    rw [← bfsForest_mapNTree, ← bfsForest_mapNTree, hM]
  have hlen : R.memoryWalkRows.length = R'.memoryWalkRows.length := by
    have := congrArg List.length hrowsM; simpa using this
  have hfb : mapNTree (projM d) (R.exec.memoryForest.get
        ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩) =
      mapNTree (projM d) (R'.exec.memoryForest.get
        ⟨0, List.length_pos_of_ne_nil R'.exec.memoryForest_nonempty⟩) := by
    have h0 := List.getElem_of_eq hM (i := 0) (by
      simpa using List.length_pos_of_ne_nil R.exec.memoryForest_nonempty)
    simpa only [List.getElem_map, List.get_eq_getElem] using h0
  unfold topologyBadGammas computeTopologyBadGammas memoryTopologyBadGammas
  congr 1
  · have hrowsC : R.computeWalkRows = R'.computeWalkRows := by
      show bfsForest [R.exec.computeTree] = bfsForest [R'.exec.computeTree]; rw [hC]
    rw [hrowsC, hC]
  · simp only
    rw [hlen]
    apply Finset.biUnion_congr rfl
    intro x _
    have e : ∀ (L : List (NTree (MState × DTmem K))) (fb : NTree (MState × DTmem K)),
        memorySlotBadGammas (L.getD x.1 fb) x.2 =
          memorySlotBadGammas ((L.map (mapNTree (projM d))).getD x.1 (mapNTree (projM d) fb)) x.2 := by
      intro L fb; rw [List.getD_map, key]
    have e1 := e R.memoryWalkRows (R.exec.memoryForest.get
        ⟨0, List.length_pos_of_ne_nil R.exec.memoryForest_nonempty⟩)
    have e2 := e R'.memoryWalkRows (R'.exec.memoryForest.get
        ⟨0, List.length_pos_of_ne_nil R'.exec.memoryForest_nonempty⟩)
    rw [e1, e2, hrowsM, hfb]

end Proj

/-! ## 3. At the package: the event template's trees read B0 ∪ B1 only -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The decoded compute environment of two truncated traces agrees where the label reads. -/
theorem decode_dTrunc_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc')
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    dTrunc (decodeSource (FamilyEnvCore.rowEnvAt P.optimized coinFree
        (FamilyEnvCore.familyQc P.optimized coinFree (truncQc P Qc)) i)) =
      dTrunc (decodeSource (FamilyEnvCore.rowEnvAt P.optimized coinFree
        (FamilyEnvCore.familyQc P.optimized coinFree (truncQc P Qc')) i)) := by
  have hv : ∀ q : VarKind × ℕ, (q.1 = .traceCur ∨ q.1 = .traceNext → srcRoundW q.2 ≤ 1) →
      Unhosted309.varVal (FamilyEnvCore.rowEnvAt P.optimized coinFree
          (FamilyEnvCore.familyQc P.optimized coinFree (truncQc P Qc)) i).toSourceEnv q.1 q.2 =
        Unhosted309.varVal (FamilyEnvCore.rowEnvAt P.optimized coinFree
          (FamilyEnvCore.familyQc P.optimized coinFree (truncQc P Qc')) i).toSourceEnv q.1 q.2 := by
    rintro ⟨k, n⟩ hq
    cases k
    · exact family_src_agree P h coinFree i n (hq (Or.inl rfl))
    · exact family_src_agree₂ P h coinFree i n (hq (Or.inr rfl))
    · rfl
    · rfl
  unfold dTrunc decodeSource
  congr 1
  · funext k
    split_ifs with hk
    · apply Unhosted309.eval_congr_reads
      intro q hq
      exact hv q (labReads_round_le q (by
        simp only [labReads, List.mem_flatMap, List.mem_range]; exact ⟨k, hk, hq⟩))
    · rfl
  all_goals
    funext k
    split_ifs with hk
    · apply Unhosted309.eval_congr_reads
      intro q hq
      exact hv q (chReads_round_le q (by
        simp only [chReads, List.mem_flatMap, List.mem_range]; exact ⟨k, hk, hq⟩))
    · rfl

/-- **The compute labels of the event strategy read B0 ∪ B1 only.** -/
theorem lblC_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc') :
    lblC P.optimized (truncQc P Qc) coinFree = lblC P.optimized (truncQc P Qc') coinFree := by
  funext j
  have hAt : ∀ i, lblCAt P.optimized (truncQc P Qc) coinFree i =
      lblCAt P.optimized (truncQc P Qc') coinFree i := by
    intro i
    have hd := decode_dTrunc_B01 P h i
    unfold lblCAt decodeInputs decodePub decodeDec
    simp only
    rw [computeStateOf_dTrunc, inpOf_dTrunc, pubOfState_dTrunc, decOf_dTrunc,
      computeStateOf_dTrunc (decodeSource _), inpOf_dTrunc (decodeSource _),
      pubOfState_dTrunc (decodeSource _), decOf_dTrunc (decodeSource _), hd]
  unfold lblC
  split_ifs <;> exact hAt _

theorem foC_B01 {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc') :
    foC P.optimized (truncQc P Qc) coinFree = foC P.optimized (truncQc P Qc') coinFree := by
  funext i; unfold foC; rw [lblC_B01 P h]

/-- The memory label's state and `pt`/`lc`/`rc` read B0 ∪ B1 only. -/
theorem lblM_proj_B01 {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm')
    (d : MState × DTmem K) (j : ℕ) :
    projM d (lblM P.optimized Qm coinFree j) = projM d (lblM P.optimized Qm' coinFree j) := by
  have hAt : ∀ i, projM d (lblMAt P.optimized Qm coinFree i) =
      projM d (lblMAt P.optimized Qm' coinFree i) := by
    intro i
    have hb : ∀ b, b < 3 → (FamilyEnvCore.memoryBaseEnvAt P.optimized coinFree Qm i).trace b =
        (FamilyEnvCore.memoryBaseEnvAt P.optimized coinFree Qm' i).trace b := fun b hb =>
      (memoryBaseEnv_agree P h i b (by unfold newMemoryColRound; simp [show b < 6 by omega])).1
    have hr : ∀ r, r < 15 → (FamilyEnvCore.memorySourceEnvAt P.optimized coinFree Qm i).trace r =
        (FamilyEnvCore.memorySourceEnvAt P.optimized coinFree Qm' i).trace r := fun r hr =>
      (memorySourceEnv_agree P h i r (by
        unfold newMemoryRoleRound DeployedStaging.memoryRoleRound
        interval_cases r <;> simp)).1
    have hst : StrategyOfTraces.memoryStateOf (FamilyEnvCore.memoryBaseEnvAt P.optimized coinFree Qm i) =
        StrategyOfTraces.memoryStateOf (FamilyEnvCore.memoryBaseEnvAt P.optimized coinFree Qm' i) := by
      unfold StrategyOfTraces.memoryStateOf
      rw [hb 0 (by omega), hb 1 (by omega), hb 2 (by omega)]
    unfold lblMAt projM decodeMemPub memoryPtNoun
    simp only
    rw [hst, hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hr 3 (by omega), hr 4 (by omega),
      hr 5 (by omega), hr 6 (by omega), hr 7 (by omega), hr 8 (by omega), hr 9 (by omega),
      hr 10 (by omega), hr 11 (by omega), hr 12 (by omega), hr 13 (by omega), hr 14 (by omega)]
  unfold lblM
  split_ifs <;> exact hAt _

theorem specialize_fst (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).1 = T.timestamp.state := by
  unfold MemoryRowTemplate.specialize MemoryRowTemplate.encodeRow MemoryRowTemplate.specializeA
  rfl

/-- The specialized round-0 memory template row, projected, is the projected decoded row. -/
theorem projM_specialize_lblMR0 (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X]) (d : MState × DTmem K) (α lmb : K) (j : ℕ) :
    projM d ((lblMR0 P.optimized Qc Qm coinFree j).specialize α lmb) =
      projM d (lblM P.optimized Qm coinFree j) := by
  unfold projM
  rw [specialize_fst, MemoryRowTemplate.specialize_pt, MemoryRowTemplate.specialize_lc,
    MemoryRowTemplate.specialize_rc]
  rfl

theorem agree_mono_C {Qc Qc' : Fin 309 → F[X]} (h : AgreeC309 1 Qc Qc') : AgreeC309 0 Qc Qc' :=
  fun j hj => h j (hj.trans (Nat.zero_le 1))

theorem agree_mono_M {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (h : AgreeM P 1 Qm Qm') :
    AgreeM P 0 Qm Qm' :=
  fun j hj => h j (hj.trans (Nat.zero_le 1))

/-- **The event template's compute tree reads B0 ∪ B1 only.** -/
theorem execTemplateEv_computeTree_B01 {Qc Qc' : Fin 309 → F[X]}
    {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hC : AgreeC309 1 Qc Qc') (hM : AgreeM P 1 Qm Qm')
    (z : K) :
    (execTemplateEv P.optimized (truncQc P Qc) Qm z).computeTree =
      (execTemplateEv P.optimized (truncQc P Qc') Qm' z).computeTree := by
  have hB0 := agreeB0_of_trace P (agree_mono_C hC) (agree_mono_M P hM)
  by_cases ht : TracesWalkHyps P.optimized (truncQc P Qc) Qm coinFree
  · have ht' := (PartAB0.tracesWalkHyps_congr hB0).1 ht
    rw [execTemplateEv_eq P.optimized _ _ ht z, execTemplateEv_eq P.optimized _ _ ht' z]
    show mapNTree StrategyOfTracesLift.wrapComputeLabel
        (reconTree (foC P.optimized (truncQc P Qc) coinFree) (lblC P.optimized (truncQc P Qc) coinFree)
          P.optimized.family.problem.cfg.compRows) =
      mapNTree StrategyOfTracesLift.wrapComputeLabel
        (reconTree (foC P.optimized (truncQc P Qc') coinFree) (lblC P.optimized (truncQc P Qc') coinFree)
          P.optimized.family.problem.cfg.compRows)
    rw [lblC_B01 P hC, foC_B01 P hC]
  · have ht' : ¬ TracesWalkHyps P.optimized (truncQc P Qc') Qm' coinFree :=
      fun t => ht ((PartAB0.tracesWalkHyps_congr hB0).2 t)
    unfold execTemplateEv
    rw [dif_neg ht, dif_neg ht']
    rfl

/-- **The event template's memory forest, specialized and projected, reads B0 ∪ B1 only.** -/
theorem execTemplateEv_memoryForest_B01 {Qc Qc' : Fin 309 → F[X]}
    {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hC : AgreeC309 1 Qc Qc') (hM : AgreeM P 1 Qm Qm')
    (d : MState × DTmem K) (z α lmb : K) :
    ((execTemplateEv P.optimized (truncQc P Qc) Qm z).specialize α lmb).memoryForest.map
        (mapNTree (projM d)) =
      ((execTemplateEv P.optimized (truncQc P Qc') Qm' z).specialize α lmb).memoryForest.map
        (mapNTree (projM d)) := by
  have hB0 := agreeB0_of_trace P (agree_mono_C hC) (agree_mono_M P hM)
  by_cases ht : TracesWalkHyps P.optimized (truncQc P Qc) Qm coinFree
  · have ht' := (PartAB0.tracesWalkHyps_congr hB0).1 ht
    rw [execTemplateEv_eq P.optimized _ _ ht z, execTemplateEv_eq P.optimized _ _ ht' z]
    show ((reconForest P.optimized.family.problem.cfg.kMem (foM P.optimized Qm coinFree)
          (lblMR0 P.optimized (truncQc P Qc) Qm coinFree) P.optimized.family.problem.cfg.memRows).map
          (mapNTree (fun row => row.specialize α lmb))).map (mapNTree (projM d)) =
      ((reconForest P.optimized.family.problem.cfg.kMem (foM P.optimized Qm' coinFree)
          (lblMR0 P.optimized (truncQc P Qc') Qm' coinFree) P.optimized.family.problem.cfg.memRows).map
          (mapNTree (fun row => row.specialize α lmb))).map (mapNTree (projM d))
    rw [mapNTree_reconForest, mapNTree_reconForest, mapNTree_reconForest, mapNTree_reconForest,
      PartAB0.foM_congr hB0]
    congr 1
    funext j
    rw [projM_specialize_lblMR0, projM_specialize_lblMR0, lblM_proj_B01 P hM]
  · have ht' : ¬ TracesWalkHyps P.optimized (truncQc P Qc') Qm' coinFree :=
      fun t => ht ((PartAB0.tracesWalkHyps_congr hB0).2 t)
    unfold execTemplateEv
    rw [dif_neg ht, dif_neg ht']
    rfl

/-- Summand 1's topology bad-`γ` set (coin `γ`, index 1; reads `αM`, `z`, `λ` = 2, 3, 10). -/
def badTopo (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K) : Finset K :=
  if hz : x 3 ≠ 0 then
    topologyBadGammas
      ((OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm).verifier.raw.afterAlphaM
        (x 3) hz (x 2) (x 10)).familyData.base
  else ∅

/-- **The topology bad set reads B0 ∪ B1 only** (the event-level congruence). -/
theorem badTopo_B01 {Qc Qc' : Fin 309 → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC309 1 Qc Qc') (hM : AgreeM P 1 Qm Qm') : badTopo P Qc Qm = badTopo P Qc' Qm' := by
  funext x
  unfold badTopo
  split_ifs with hz
  · obtain d := lblM P.optimized Qm coinFree 1
    apply topologyBadGammas_congr_proj _ _ d
    · exact congrArg (mapNTree fun row => row.specialize (x 2))
        (execTemplateEv_computeTree_B01 P hC hM (x 3))
    · exact execTemplateEv_memoryForest_B01 P hC hM d (x 3) (x 2) (x 10)
  · rfl

theorem badTopo_coins (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    ReadsOn (C := K) ({2, 3, 10} : Finset (Fin 12)) (badTopo P Qc Qm) := by
  intro x y h
  unfold badTopo
  rw [h 2 (by simp), h 3 (by simp), h 10 (by simp)]

theorem badTopo_card (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K) :
    (badTopo P Qc Qm x).card ≤
      24 * P.optimized.family.problem.cfg.compRows + 8 * P.optimized.family.problem.cfg.memRows := by
  unfold badTopo
  split_ifs with hz
  · refine (topologyBadGammas_card_le _).trans ?_
    rw [P8EventEv.topologyWorkload_afterAlphaM,
      show (P8EventEv.seedConfig (OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm) (x 3) hz).compRows =
        P.optimized.family.problem.cfg.compRows from
      committedTemplate_Ev_compRows P.optimized (truncQc P Qc) Qm P.stateTagChar (x 3) hz,
      show (P8EventEv.seedConfig (OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm) (x 3) hz).memRows =
        P.optimized.family.problem.cfg.memRows from
      committedTemplate_Ev_memRows P.optimized (truncQc P Qc) Qm P.stateTagChar (x 3) hz]
    omega
  · simp

theorem mem_topo (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) (x : Fin 12 → K)
    (h : tuple12OfVec (F := F) x ∈ cyl12 (OptimizedFailureEventEv.p8SlotEv P (truncQc P Qc) Qm)) :
    (tuple12OfVec (F := F) x).1 ∈ PartAB0.m1Part (OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm)
        P.optimized.Λ (x 10) ∨ x 1 ∈ badTopo P Qc Qm x := by
  rw [mem_cyl12, OptimizedFailureEventEv.mem_p8SlotEv_iff, PartAB0.evFailureUnion_split,
    Finset.mem_union] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [mem_specializedTopologyFailureEvent_iff] at h
    obtain ⟨hz, hg⟩ := h
    have hz' : x 3 ≠ 0 := hz
    unfold badTopo
    rw [dif_pos hz']
    exact hg

end Package

end

end Nock.NockVMROM.Thm54.PartAStaged
