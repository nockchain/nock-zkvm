import Nock.NockVMROM.Thm54.P8Core.OptimizedFailureEventEv
import Nock.NockVMROM.Thm54.P8Core.DeployedStaging
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
import Nock.NockVMROM.Thm54.P8Core.RepartitionedStaging
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/NockVMROM/Thm54/P8Core/PartAB0Locality.lean

  **The B0 / env-level read-set congruences of lanes L0 and L1,
  promoted VERBATIM to a production module** so that the staged theorem (`PartAStaged12`) can
  consume them (production code may not import `Nock/RedTeam`).  Sources, proofs unchanged, only
  the namespace moved (`Nock.RedTeam.Batch1408` / `Nock.RedTeam.Batch1409` →
  `Nock.NockVMROM.Thm54.PartAB0`):

  The decide-level round receipts of those batches stay in `Nock/RedTeam` (they are not
  consumed).  Scope: the repartitioned schedule and the parallel
  package
-/
open Nock Nock.Reified Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54.TemplateAxisCounting Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier Nock.NockVMROM.Thm54.ProductionP8Containment
open Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option quotPrecheck false

namespace Nock.NockVMROM.Thm54.PartAB0
/-! ## §1  The read-set instrument on the compute decoder -/

/-- Current-row trace columns an expression reads. -/
def curCols : Expr → List ℕ
  | .Var .traceCur i => [i]
  | .Var _ _ => []
  | .Const _ => []
  | .Add a b => curCols a ++ curCols b
  | .Sub a b => curCols a ++ curCols b
  | .Mul a b => curCols a ++ curCols b
  | .Neg a => curCols a
  | .Pow a _ => curCols a

theorem eval_congr_of_curCols {K : Type} [Field K] (e : Expr) {E E' : Env K}
    (ht : ∀ k ∈ curCols e, E.trace k = E'.trace k)
    (he : FamilyChipTwins.traceOnly e = true) : e.eval E = e.eval E' := by
  induction e with
  | Var kind i =>
      cases kind
      · simp only [Expr.eval]; exact ht i (by simp [curCols])
      all_goals simp [FamilyChipTwins.traceOnly] at he
  | Const c => rfl
  | Add a b iha ihb =>
      simp only [FamilyChipTwins.traceOnly, Bool.and_eq_true] at he
      simp only [Expr.eval]
      rw [iha (fun k hk => ht k (by simp [curCols, hk])) he.1,
        ihb (fun k hk => ht k (by simp [curCols, hk])) he.2]
  | Sub a b iha ihb =>
      simp only [FamilyChipTwins.traceOnly, Bool.and_eq_true] at he
      simp only [Expr.eval]
      rw [iha (fun k hk => ht k (by simp [curCols, hk])) he.1,
        ihb (fun k hk => ht k (by simp [curCols, hk])) he.2]
  | Mul a b iha ihb =>
      simp only [FamilyChipTwins.traceOnly, Bool.and_eq_true] at he
      simp only [Expr.eval]
      rw [iha (fun k hk => ht k (by simp [curCols, hk])) he.1,
        ihb (fun k hk => ht k (by simp [curCols, hk])) he.2]
  | Neg a ih =>
      simp only [FamilyChipTwins.traceOnly] at he
      simp only [Expr.eval]; rw [ih (fun k hk => ht k (by simp [curCols, hk])) he]
  | Pow a n ih =>
      simp only [FamilyChipTwins.traceOnly] at he
      simp only [Expr.eval]; rw [ih (fun k hk => ht k (by simp [curCols, hk])) he]

/-- The compute source columns the `z`/`αM` sub-events of `p8SlotEv` read (compiled below): the
state selectors `0..10`, the Form R certificate block `202..270`, the carrier `S` = `302`. -/
def computeB0Reads : List ℕ := List.range 11 ++ List.range' 202 69 ++ [302]


/-! ## §2  Generic congruences on a finer read set (the certificate axis, the skeleton consumers) -/

section CertAxis
variable {K : Type} [Field K] [DecidableEq K] {N : ℕ}

/-- Agreement of two compute source-env families on `computeB0Reads`. -/
def AgreeC (envsC envsC' : Fin N → Env K) : Prop :=
  ∀ i, ∀ k ∈ computeB0Reads, (envsC i).trace k = (envsC' i).trace k

theorem mem_computeB0Reads_lt11 {k : ℕ} (hk : k < 11) : k ∈ computeB0Reads := by
  simp [computeB0Reads]; omega
theorem mem_computeB0Reads_cert {k : ℕ} (h1 : 202 ≤ k) (h2 : k ≤ 270) : k ∈ computeB0Reads := by
  simp [computeB0Reads]; omega

theorem computeArity_congr' {E E' : Env K} (h : ∀ k ∈ computeB0Reads, E.trace k = E'.trace k) :
    DecodedLambdaEvent.computeArity E = DecodedLambdaEvent.computeArity E' := by
  unfold DecodedLambdaEvent.computeArity
  rw [h 0 (by decide), h 2 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
    h 8 (by decide), h 9 (by decide)]

theorem computePrefix_congr' {envsC envsC' : Fin N → Env K} (h : AgreeC envsC envsC') (i : Fin N) :
    DecodedLambdaEvent.computePrefix envsC i = DecodedLambdaEvent.computePrefix envsC' i := by
  unfold DecodedLambdaEvent.computePrefix
  exact Finset.sum_congr rfl fun j _ => computeArity_congr' (h j)

theorem locateExp_congr' {envsC envsC' : Fin N → Env K} (h : AgreeC envsC envsC') (e : ℕ) :
    DecodedLambdaEvent.locateExp envsC e = DecodedLambdaEvent.locateExp envsC' e := by
  have hp : (fun i : Fin N => decide (DecodedLambdaEvent.computePrefix envsC i < e ∧
      e ≤ DecodedLambdaEvent.computePrefix envsC i + DecodedLambdaEvent.computeArity (envsC i))) =
      fun i : Fin N => decide (DecodedLambdaEvent.computePrefix envsC' i < e ∧
      e ≤ DecodedLambdaEvent.computePrefix envsC' i + DecodedLambdaEvent.computeArity (envsC' i)) := by
    funext i
    rw [computePrefix_congr' h i, computeArity_congr' (h i)]
  unfold DecodedLambdaEvent.locateExp
  rw [hp]
  congr 1
  funext i
  rw [computePrefix_congr' h i]

theorem rowShift_congr' {E E' : Env K} (h : ∀ k ∈ computeB0Reads, E.trace k = E'.trace k) :
    DecodedLambdaEvent.rowShift E = DecodedLambdaEvent.rowShift E' := by
  unfold DecodedLambdaEvent.rowShift
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk6 : k < 6 := Finset.mem_range.mp hk
  rw [h (265 + k) (mem_computeB0Reads_cert (by omega) (by omega))]

theorem rowBits_congr' {E E' : Env K} (h : ∀ k ∈ computeB0Reads, E.trace k = E'.trace k) :
    DecodedLambdaEvent.rowBits E = DecodedLambdaEvent.rowBits E' := by
  funext k
  unfold DecodedLambdaEvent.rowBits
  by_cases hk : 1 ≤ k ∧ k ≤ 63
  · rw [h (202 + (k - 1)) (mem_computeB0Reads_cert (by omega) (by omega))]
  · have : ¬ (1 ≤ k ∧ k ≤ 63 ∧ E.trace (202 + (k - 1)) = 1) := fun h' => hk ⟨h'.1, h'.2.1⟩
    have h' : ¬ (1 ≤ k ∧ k ≤ 63 ∧ E'.trace (202 + (k - 1)) = 1) := fun h' => hk ⟨h'.1, h'.2.1⟩
    simp only [this, h', decide_false]

theorem slotCert_congr' {envsC envsC' : Fin N → Env K} (h : AgreeC envsC envsC') (i : Fin N) (j : ℕ) :
    DecodedLambdaEvent.slotCert envsC i j = DecodedLambdaEvent.slotCert envsC' i j := by
  unfold DecodedLambdaEvent.slotCert
  rw [h i 0 (by decide), h i 9 (by decide), rowShift_congr' (h i), rowBits_congr' (h i)]

theorem decodedShift_congr' {envsC envsC' : Fin N → Env K} (h : AgreeC envsC envsC') (e : ℕ) :
    DecodedLambdaEvent.decodedShift envsC e = DecodedLambdaEvent.decodedShift envsC' e := by
  unfold DecodedLambdaEvent.decodedShift
  rw [locateExp_congr' h e]
  split
  · rw [slotCert_congr' h]
  · rfl

theorem decodedBits_congr' {envsC envsC' : Fin N → Env K} (h : AgreeC envsC envsC') (e : ℕ) :
    DecodedLambdaEvent.decodedBits envsC e = DecodedLambdaEvent.decodedBits envsC' e := by
  funext k
  unfold DecodedLambdaEvent.decodedBits
  rw [locateExp_congr' h e]
  split
  · rw [slotCert_congr' h]
  · rfl

/-- **The certificate axis reads `computeB0Reads` only** (finer than `certAxisOfEnvs_congr`, which
assumes the whole trace). -/
theorem certAxisOfEnvs_congr' {envsC envsC' : Fin N → Env K} (h : AgreeC envsC envsC') (e : ℕ) :
    certAxisOfEnvs envsC e = certAxisOfEnvs envsC' e := by
  unfold certAxisOfEnvs
  rw [decodedShift_congr' h e, decodedBits_congr' h e]

end CertAxis

section Skeleton

/-- The three `z`-coin consumers of a skeleton read its compute tree only. -/
theorem combinedSkeletonPairs_congr (K : Type) [Field K] {S S' : SemanticSkeleton}
    (h : S.computeTree = S'.computeTree) :
    EdgeComparisonCensus.combinedSkeletonPairs K S = EdgeComparisonCensus.combinedSkeletonPairs K S' := by
  have hrows : computeSkeletonRows S = computeSkeletonRows S' := by
    unfold computeSkeletonRows; rw [h]
  have hclaim : S.publicClaim = S'.publicClaim := by
    unfold SemanticSkeleton.publicClaim; rw [h]
  unfold EdgeComparisonCensus.combinedSkeletonPairs BoundSemanticTrace.skeletonPairs
    P8Census.skeletonComparisonCensus
  rw [h, hclaim, hrows]

theorem skeletonSizeWindowNouns_congr {S S' : SemanticSkeleton}
    (h : S.computeTree = S'.computeTree) :
    SizeWindowCounting.skeletonSizeWindowNouns S = SizeWindowCounting.skeletonSizeWindowNouns S' := by
  unfold SizeWindowCounting.skeletonSizeWindowNouns computeSkeletonRows; rw [h]

end Skeleton

/-! ## §3  Over a package: the `z`-coin sub-events of `p8SlotEv` read B0 only -/

section OverO

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

variable (Qc Qc' : Fin (CC[O]).rap.w → F[X]) (Qm Qm' : Fin (MC[O]).rap.w → F[X])

/-- **B0 agreement** of two trace pairs, at the row-environment level the event-side strategy
reads (`computeEnvsR0`, `memoryEnvsR0` at `coinFree`): compute source columns `computeB0Reads`,
memory base columns `preZMemCols`.  Every listed column is round 0 on both schedules
(`computeB0Reads_round0`, `memB0Reads_round0`). -/
def AgreeB0 : Prop :=
  AgreeC (computeEnvsR0 O Qc coinFree) (computeEnvsR0 O Qc' coinFree) ∧
    ∀ i, ∀ b ∈ PreZComputeCore.Served.preZMemCols,
      (memoryEnvsR0 O Qm coinFree i).trace b = (memoryEnvsR0 O Qm' coinFree i).trace b

variable {O Qc Qc' Qm Qm'}

theorem lblC_state_congr (h : AgreeC (computeEnvsR0 O Qc coinFree) (computeEnvsR0 O Qc' coinFree))
    (j : ℕ) : (lblC O Qc coinFree j).1 = (lblC O Qc' coinFree j).1 := by
  unfold lblC
  split_ifs <;>
  · unfold lblCAt
    apply computeStateOf_congr
    intro k hk
    show (computeTraceSubst .traceCur k).eval _ = (computeTraceSubst .traceCur k).eval _
    apply eval_congr_of_curCols
    · intro s hs
      have hsk : s = k := by
        have : curCols (computeTraceSubst .traceCur k) = [k] := by
          simp [computeTraceSubst, hk, curCols]
        rw [this] at hs; simpa using hs
      subst hsk
      exact h _ s (mem_computeB0Reads_lt11 hk)
    · simp [computeTraceSubst, hk, FamilyChipTwins.traceOnly]

theorem foC_congr (h : AgreeC (computeEnvsR0 O Qc coinFree) (computeEnvsR0 O Qc' coinFree)) :
    foC O Qc coinFree = foC O Qc' coinFree := by
  funext i; unfold foC; rw [lblC_state_congr h i]

theorem c2SAt_congr (h : AgreeC (computeEnvsR0 O Qc coinFree) (computeEnvsR0 O Qc' coinFree))
    (i : Fin O.family.problem.cfg.compRows) : c2SAt O Qc coinFree i = c2SAt O Qc' coinFree i := by
  unfold c2SAt; rw [h i 302 (by simp [computeB0Reads])]

theorem c2TreeOfTraces_proj_congr
    (h : AgreeC (computeEnvsR0 O Qc coinFree) (computeEnvsR0 O Qc' coinFree)) :
    mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2)) (c2TreeOfTraces O Qc coinFree) =
      mapNTree (fun l : (State × DTcomp K) × ℕ => (l.1.1, l.2)) (c2TreeOfTraces O Qc' coinFree) := by
  unfold c2TreeOfTraces reconTree
  rw [mapNTree_buildT', mapNTree_buildT', foC_congr h]
  congr 1
  funext j
  unfold lblCS
  split_ifs
  · rw [lblC_state_congr h j, c2SAt_congr h]
  · rw [lblC_state_congr h j, c2SAt_congr h]

/-- **The env-level hypothesis is polynomial-level B0 agreement (compute side).**  If the two
compute traces agree as polynomials on the physical columns `computeB0Reads` (all round 0), the
source envs agree there. -/
theorem agreeC_of_poly
    (h : ∀ j : Fin (CC[O]).rap.w, (j : ℕ) ∈ computeB0Reads → Qc j = Qc' j) :
    AgreeC (computeEnvsR0 O Qc coinFree) (computeEnvsR0 O Qc' coinFree) := by
  intro i k hk
  have hE : ∀ k ∈ computeB0Reads, ∀ (x : F) (ch pb : ℕ → F),
      (Nock.Framework.Reify.envOfTrace (FamilyEnvCore.familyQc O coinFree Qc) O.orbit.ω x ch pb).trace k =
        (Nock.Framework.Reify.envOfTrace (FamilyEnvCore.familyQc O coinFree Qc') O.orbit.ω x ch pb).trace k := by
    intro k hk x ch pb
    rw [FamilyEnvCore.familyQc_envTrace, FamilyEnvCore.familyQc_envTrace]
    simp only [Nock.Framework.Reify.envOfTrace]
    split_ifs with hw
    · rw [h ⟨k, hw⟩ hk]
    · rfl
  unfold computeEnvsR0 FamilyEnvCore.rowEnvAt
  simp only [CorrectedFinalTypedEnv.toSourceEnv, OptimizedComputeSemanticRealization.gatherCorrectedFinalTypedEnv]
  have hk' : k < 11 ∨ (202 ≤ k ∧ k < 271) ∨ k = 302 := by
    simp only [computeB0Reads, List.mem_append, List.mem_range, List.mem_range'_1,
      List.mem_singleton] at hk
    omega
  split_ifs with h1 h2 h3 h4 h5 h6
  · rw [hE k hk]
  · omega
  · have e : 202 + (k - 202) = k := by omega
    simp only [e]; rw [hE k hk]
  · omega
  · omega
  · rw [hE 302 (by simp [computeB0Reads])]
  · omega

/-- **The event skeleton's compute tree reads B0 only** (across traces, not only across coins). -/
theorem c2ComputeTree_congr (h : AgreeB0 O Qc Qc' Qm Qm') :
    c2ComputeTree O Qc Qm coinFree = c2ComputeTree O Qc' Qm' coinFree := by
  unfold c2ComputeTree c2Join
  rw [c2JoinFuel_factor, c2JoinFuel_factor (t := c2TreeOfTraces O Qc' coinFree)]
  have hproj := c2TreeOfTraces_proj_congr h.1
  have hsize : (c2TreeOfTraces O Qc coinFree).size = (c2TreeOfTraces O Qc' coinFree).size := by
    have := congrArg NTree.size hproj
    rwa [ReconTreeSize.size_mapNTree, ReconTreeSize.size_mapNTree] at this
  have hsv : c2ServedOf O Qm coinFree = c2ServedOf O Qm' coinFree :=
    PreZComputeCore.Served.servedNounOfEnvs_congr K _ _ h.2 _
  have hax : c2AxOf O Qc coinFree = c2AxOf O Qc' coinFree := by
    funext e; exact certAxisOfEnvs_congr' h.1 e
  rw [hsize, hproj, hsv, hax]

theorem skeletonEv_computeTree_congr (tag : NodeEncoding.StateTagChar K) (h : AgreeB0 O Qc Qc' Qm Qm') :
    (strategyOfTracesEv O Qc Qm tag).skeleton.computeTree =
      (strategyOfTracesEv O Qc' Qm' tag).skeleton.computeTree :=
  c2ComputeTree_congr h

/-- **R1, sub-events 1, 2, 5 of `p8SlotEv` (coin `z`, M1): B0 only.**  The zero-seed event, the
guarded census's collisions and the guarded size windows at the event strategy are equal for any
two trace pairs agreeing on B0. -/
theorem p8_seed_subevents_B0 (tag : NodeEncoding.StateTagChar K) (Λ : ℕ) (h : AgreeB0 O Qc Qc' Qm Qm') :
    collisionFailureEvent (K := K) (guardedCensusEv K (strategyOfTracesEv O Qc Qm tag).skeleton Λ) =
        collisionFailureEvent (K := K) (guardedCensusEv K (strategyOfTracesEv O Qc' Qm' tag).skeleton Λ) ∧
      guardedSizeWindowFailure (K := K) (strategyOfTracesEv O Qc Qm tag).skeleton Λ =
        guardedSizeWindowFailure (K := K) (strategyOfTracesEv O Qc' Qm' tag).skeleton Λ := by
  have hT := skeletonEv_computeTree_congr tag h
  refine ⟨?_, ?_⟩
  · unfold guardedCensusEv; rw [combinedSkeletonPairs_congr K hT]
  · unfold guardedSizeWindowFailure guardedSizeWindowSeeds; rw [skeletonSizeWindowNouns_congr hT]

/-! ## §4  The `αM` sub-event (envelope axis share, coin `αM` = timestamp role, M1): B0 only -/

theorem lblM_state_congr (h : AgreeB0 O Qc Qc' Qm Qm') (j : ℕ) :
    (lblM O Qm coinFree j).1 = (lblM O Qm' coinFree j).1 := by
  have key : ∀ i, StrategyOfTraces.memoryStateOf (FamilyEnvCore.memoryBaseEnvAt O coinFree Qm i) =
      StrategyOfTraces.memoryStateOf (FamilyEnvCore.memoryBaseEnvAt O coinFree Qm' i) := by
    intro i
    have h0 := h.2 i 0 (by decide)
    have h1 := h.2 i 1 (by decide)
    have h2 := h.2 i 2 (by decide)
    simp only [memoryEnvsR0] at h0 h1 h2
    unfold StrategyOfTraces.memoryStateOf
    rw [h0, h1, h2]
  unfold lblM lblMAt
  split_ifs <;> exact key _

theorem foM_congr (h : AgreeB0 O Qc Qc' Qm Qm') : foM O Qm coinFree = foM O Qm' coinFree := by
  funext i; unfold foM; rw [lblM_state_congr h i]

theorem tracesWalkHyps_congr (h : AgreeB0 O Qc Qc' Qm Qm') :
    TracesWalkHyps O Qc Qm coinFree ↔ TracesWalkHyps O Qc' Qm' coinFree := by
  have hC := foC_congr h.1
  have hM := foM_congr h
  constructor
  · intro t
    exact ⟨by rw [← hC]; exact t.sfCompute, by rw [← hC]; exact t.validCompute,
      by rw [← hM]; exact t.sfMemory, by rw [← hM]; exact t.validMemory⟩
  · intro t
    exact ⟨by rw [hC]; exact t.sfCompute, by rw [hC]; exact t.validCompute,
      by rw [hM]; exact t.sfMemory, by rw [hM]; exact t.validMemory⟩

/-- The projection the axis tree sees: timestamp metadata, the state, and the stored axis; every
other placeholder field is overwritten by the fixed `d`. -/
def axisProj (d : MState × DTmem K) (T : MemoryRowTemplate (K := K)) : MemoryRowTemplate (K := K) :=
  { timestamp := T.timestamp
    placeholder := (T.placeholder.1, (d.2.1,
      { d.2.2 with mem := { d.2.2.mem with axis := T.placeholder.2.2.mem.axis } })) }

theorem axisTree_axisProj (d : MState × DTmem K) (t : NTree (MemoryRowTemplate (K := K))) :
    templateAxisTree (mapNTree (axisProj d) t) = templateAxisTree t :=
  templateAxisTree_mapNTree (axisProj d) (fun _ => rfl) (fun _ => rfl) t

theorem axisProj_lblMR0_congr (h : AgreeB0 O Qc Qc' Qm Qm') (d : MState × DTmem K) (j : ℕ) :
    axisProj d (lblMR0 O Qc Qm coinFree j) = axisProj d (lblMR0 O Qc' Qm' coinFree j) := by
  have hst := lblM_state_congr h j
  have hexp : memRowExpOfEnvs (memoryEnvsR0 O Qm coinFree) O.family.problem.cfg.memRows_pos j =
      memRowExpOfEnvs (memoryEnvsR0 O Qm' coinFree) O.family.problem.cfg.memRows_pos j := by
    unfold memRowExpOfEnvs
    split_ifs <;> rw [h.2 _ OptimizedMemoryGateBasis.reqIdxCol (by simp [PreZComputeCore.Served.preZMemCols])]
  have hax := certAxisOfEnvs_congr' h.1
    (memRowExpOfEnvs (memoryEnvsR0 O Qm' coinFree) O.family.problem.cfg.memRows_pos j)
  unfold lblMR0 wrapR0OfEnvs wrapMemoryLabelR0 axisProj
  rw [hexp, hax, hst]

/-- **The event template's memory forest, seen by the axis tree, reads B0 only.** -/
theorem execTemplateEv_axisForest_congr (h : AgreeB0 O Qc Qc' Qm Qm') (z : K) :
    (execTemplateEv O Qc Qm z).memoryForest.map templateAxisTree =
      (execTemplateEv O Qc' Qm' z).memoryForest.map templateAxisTree := by
  by_cases ht : TracesWalkHyps O Qc Qm coinFree
  · have ht' := (tracesWalkHyps_congr h).1 ht
    rw [execTemplateEv_eq O Qc Qm ht z, execTemplateEv_eq O Qc' Qm' ht' z]
    show (reconForest O.family.problem.cfg.kMem (foM O Qm coinFree) (lblMR0 O Qc Qm coinFree)
        O.family.problem.cfg.memRows).map templateAxisTree =
      (reconForest O.family.problem.cfg.kMem (foM O Qm' coinFree) (lblMR0 O Qc' Qm' coinFree)
        O.family.problem.cfg.memRows).map templateAxisTree
    let d := lblM O Qm coinFree 0
    have hL : ∀ L : List (NTree (MemoryRowTemplate (K := K))),
        L.map templateAxisTree = (L.map (mapNTree (axisProj d))).map templateAxisTree := by
      intro L
      rw [List.map_map]
      exact List.map_congr_left fun t _ => (axisTree_axisProj d t).symm
    rw [hL, hL (reconForest _ _ (lblMR0 O Qc' Qm' coinFree) _), ReconTreeSize.mapNTree_reconForest,
      ReconTreeSize.mapNTree_reconForest, foM_congr h]
    congr 2
    funext j
    exact axisProj_lblMR0_congr h d j
  · have ht' : ¬ TracesWalkHyps O Qc' Qm' coinFree := fun t => ht ((tracesWalkHyps_congr h).2 t)
    unfold execTemplateEv
    rw [dif_neg ht, dif_neg ht']
    rfl

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] in
theorem heq_fin_funs {β : Type} {a b : ℕ} (h : a = b) (f : ℕ → β) :
    HEq (fun i : Fin a => f i) (fun i : Fin b => f i) := by subst h; rfl

theorem cfgTemplateOfTraces_congr (z : K) :
    cfgTemplateOfTraces O Qc Qm coinFree z = cfgTemplateOfTraces O Qc' Qm' coinFree z := by
  have h1 : cfgOfTraces O Qc Qm coinFree = cfgOfTraces O Qc' Qm' coinFree := by
    unfold cfgOfTraces
    have hc : (computeLabelList O Qc coinFree).length = (computeLabelList O Qc' coinFree).length := by
      rw [computeLabelList_length, computeLabelList_length]
    have hm : (memoryLabelList O Qm coinFree).length = (memoryLabelList O Qm' coinFree).length := by
      rw [memoryLabelList_length, memoryLabelList_length]
    congr 1
    all_goals first
      | exact hc | exact hm | exact proof_irrel_heq _ _
      | exact heq_fin_funs hc (fun i => O.family.problem.cfg.orbit.βcoset * O.family.problem.cfg.orbit.ω ^ i)
      | exact heq_fin_funs hm (fun i => O.family.problem.cfg.orbit.βcoset * O.family.problem.cfg.orbit.ω ^ i)
  unfold cfgTemplateOfTraces
  rw [h1]

end OverO

section Envelope
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]

/-- **Generic: the envelope union reads the axis trees only.** -/
theorem envelopeRootUnion_congr_axis {T : ExactConfigTemplate F K} (E E' : ExactExecutionTemplate T)
    (lmb : K) (hax : ∀ i, templateAxisTree (templateMemoryTreeAt E i) =
      templateAxisTree (templateMemoryTreeAt E' i)) :
    envelopeRootUnion E lmb = envelopeRootUnion E' lmb := by
  have hpoly : ∀ i, templateAxisPolynomial E i = templateAxisPolynomial E' i := by
    intro i; unfold templateAxisPolynomial; rw [hax i]
  have hroot : ∀ i, alphaFreeRoot E i = alphaFreeRoot E' i := hax
  have hcheck : alphaFreeAxisStructureCheck E = alphaFreeAxisStructureCheck E' := by
    unfold alphaFreeAxisStructureCheck forestExponentPartitionCheck templateForestReadExps
      templateForestVerifyExps
    simp only [hroot, hax]
  have hwrap : ∀ α, noWrapCheck E α = noWrapCheck E' α := by
    intro α; unfold noWrapCheck; simp only [hroot]
  have hguard : ∀ i, verifierGuardedRootAlphas E lmb i = verifierGuardedRootAlphas E' lmb i := by
    intro i
    unfold verifierGuardedRootAlphas
    apply Finset.filter_congr
    intro α _
    rw [exactAxisTree_specialize, exactAxisTree_specialize,
      recoveredAxisTree_eq_reindexAxisTree, recoveredAxisTree_eq_reindexAxisTree,
      hcheck, hwrap α, hax i, hpoly i]
  unfold envelopeRootUnion envelopeRootAlphas
  apply Finset.biUnion_congr rfl
  intro i _
  rw [hpoly i, hguard i]

/-- Across two equal config templates, with the axis-tree images of the memory forests equal. -/
theorem envelopeRootUnion_congr_forest {T T' : ExactConfigTemplate F K} (hT : T = T')
    (E : ExactExecutionTemplate T) (E' : ExactExecutionTemplate T') (lmb : K)
    (hF : E.memoryForest.map templateAxisTree = E'.memoryForest.map templateAxisTree) :
    envelopeRootUnion E lmb = envelopeRootUnion E' lmb := by
  subst hT
  apply envelopeRootUnion_congr_axis
  intro i
  unfold templateMemoryTreeAt
  have hlen : E.memoryForest.length = E'.memoryForest.length := by
    have := congrArg List.length hF; simpa using this
  have := congrArg (fun L => L[(i : ℕ)]?) hF
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem (by rw [E.memory_root_count]; exact i.2),
    List.getElem?_eq_getElem (by rw [E'.memory_root_count]; exact i.2)] at this
  simpa using this

end Envelope

section OverO2

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} {O : OptimizedStrictNockVMROMPackage F K hOrb}

local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

variable {Qc Qc' : Fin (CC[O]).rap.w → F[X]} {Qm Qm' : Fin (MC[O]).rap.w → F[X]}

/-- **R1, sub-event 4 of `p8SlotEv` (the envelope axis share; free coin `αM`, the timestamp base,
M1 at the repartitioned schedule; it also reads `z`, `λ` directly): B0 only.** -/
theorem p8_envelope_subevent_B0 (tag : NodeEncoding.StateTagChar K) (lmb : K)
    (h : AgreeB0 O Qc Qc' Qm Qm') :
    envelopeAxisFailureEvent (strategyOfTracesEv O Qc Qm tag) lmb =
      envelopeAxisFailureEvent (strategyOfTracesEv O Qc' Qm' tag) lmb := by
  ext ω
  rw [mem_envelopeAxisFailureEvent_iff, mem_envelopeAxisFailureEvent_iff]
  have hU : ∀ z (hz : z ≠ 0),
      envelopeRootUnion (committedTemplate (strategyOfTracesEv O Qc Qm tag).verifier z hz) lmb =
        envelopeRootUnion (committedTemplate (strategyOfTracesEv O Qc' Qm' tag).verifier z hz) lmb := by
    intro z hz
    rw [committedTemplate_Ev, committedTemplate_Ev]
    exact envelopeRootUnion_congr_forest (cfgTemplateOfTraces_congr z) _ _ lmb
      (execTemplateEv_axisForest_congr h z)
  constructor
  · rintro ⟨hz, hα⟩; exact ⟨hz, by rwa [← hU _ hz]⟩
  · rintro ⟨hz, hα⟩; exact ⟨hz, by rwa [hU _ hz]⟩

end OverO2


/-! ## §5  Summand 11 (the decoded λ-event, coins `(αM, λ)`, both M1): compiled B0 locality -/

section Lambda
open DecodedLambdaEvent
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}

/-- The memory base columns summand 11 reads: selectors `0..2`, `reqIdx` = `181`. -/
def lamMemReads : List ℕ := [0, 1, 2, 181]

theorem lamMemReads_round0 : ∀ b ∈ lamMemReads, memoryColRound b = 0 := by decide

theorem measure_ind (M : ℕ) (P : ℕ → Prop)
    (step : ∀ i, (∀ c, i < c → 1 ≤ i → i ≤ M → P c) → P i) : ∀ i, P i := by
  have key : ∀ d i, M + 1 - i ≤ d → P i := by
    intro d
    induction d with
    | zero => intro i hi; exact step i fun c _ h1 h2 => absurd hi (by omega)
    | succ d ih =>
        intro i hi
        exact step i fun c hc h1 h2 => ih c (by omega)
  exact fun i => key _ i le_rfl

theorem decodedMTreeOfEnvs_congr {envsK envsK' : Fin M → Env K} {envsF envsF' : Fin M → Env F}
    (hF : ∀ i, ∀ b ∈ lamMemReads, (envsF i).trace b = (envsF' i).trace b) (kroots : ℕ) :
    ∀ i, decodedMTreeOfEnvs envsK envsF kroots i = decodedMTreeOfEnvs envsK' envsF' kroots i := by
  have hst : ∀ r, WalkTilingEvents.memRowStateOf (envsF r) = WalkTilingEvents.memRowStateOf (envsF' r) := by
    intro r
    unfold WalkTilingEvents.memRowStateOf
    rw [hF r 0 (by decide), hF r 1 (by decide), hF r 2 (by decide)]
  have hfo : WalkTilingEvents.foOfMem envsF = WalkTilingEvents.foOfMem envsF' := by
    funext i; unfold WalkTilingEvents.foOfMem; split_ifs <;> simp [hst]
  have hci : childIdx envsF = childIdx envsF' := by
    funext kr i l; unfold childIdx; rw [hfo]
  have hexp : rowExp envsF = rowExp envsF' := by
    funext r; unfold rowExp; rw [hF r 181 (by decide)]
  refine measure_ind M _ fun i ih => ?_
  conv_lhs => rw [decodedMTreeOfEnvs]
  conv_rhs => rw [decodedMTreeOfEnvs]
  by_cases h : 1 ≤ i ∧ i ≤ M
  · rw [dif_pos h, dif_pos h, hst, hexp, hci]
    have hc : ∀ l, (if i < childIdx envsF' kroots i l then
        decodedMTreeOfEnvs envsK envsF kroots (childIdx envsF' kroots i l) else MTree.halt) =
        (if i < childIdx envsF' kroots i l then
        decodedMTreeOfEnvs envsK' envsF' kroots (childIdx envsF' kroots i l) else MTree.halt) := by
      intro l
      by_cases hl : i < childIdx envsF' kroots i l
      · rw [if_pos hl, if_pos hl]; exact ih _ hl h.1 h.2
      · rw [if_neg hl, if_neg hl]
    rw [hc 1, hc 2]
  · rw [dif_neg h, dif_neg h]

/-- **Summand 11 is env-local on round-0 columns only**: compute `computeB0Reads` (it reads
`0, 2, 5..9, 202..270` of them), memory base `0, 1, 2, 181`, and NO `𝕂` role (`envsK` arbitrary). -/
theorem decodedLambdaEventOfEnvs_congr {envsC envsC' : Fin N → Env K}
    {envsK envsK' : Fin M → Env K} {envsF envsF' : Fin M → Env F}
    (hC : AgreeC envsC envsC') (hF : ∀ i, ∀ b ∈ lamMemReads, (envsF i).trace b = (envsF' i).trace b)
    (kroots : ℕ) :
    decodedLambdaEventOfEnvs envsC envsK envsF kroots =
      decodedLambdaEventOfEnvs envsC' envsK' envsF' kroots := by
  have hsh : decodedShift envsC = decodedShift envsC' := funext fun e => decodedShift_congr' hC e
  have hbi : decodedBits envsC = decodedBits envsC' := funext fun e => decodedBits_congr' hC e
  have hroot : ∀ r, decodedRootBad envsC envsK envsF kroots r =
      decodedRootBad envsC' envsK' envsF' kroots r := by
    intro r
    unfold decodedRootBad decodedRootPoly
    rw [hsh, hbi, decodedMTreeOfEnvs_congr (envsK' := envsK') hF kroots r]
  unfold decodedLambdaEventOfEnvs
  simp only [hroot]

/-- The tie to the consumed summand (`rfl`). -/
theorem tie11 {hOrb : ℕ} [CharP K (ringChar K)] [FiniteDimensional F K]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.decodedLambdaEventOf Qc Qm =
      decodedLambdaEventOfEnvs (P.computeSourceEnv Qc) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)
        P.optimized.family.problem.cfg.kMem := rfl

end Lambda

/-! ## §7  The p8 slot assembled: its M1 part reads B0 only -/

section Slot
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-- The M1-coin part of `evFailureUnion`: every sub-event but the topology (`γ`, M2) one. -/
noncomputable def m1Part (T : ProductionStrategy F K) (Λ : ℕ) (lmb : K) : Finset (JointCoins K) :=
  ((zeroSeedFailureEvent ∪ collisionFailureEvent (guardedCensusEv K T.skeleton Λ)) ∪
    envelopeAxisFailureEvent T lmb) ∪ guardedSizeWindowFailure T.skeleton Λ

theorem evFailureUnion_split (T : ProductionStrategy F K) (Λ : ℕ) (lmb : K) :
    evFailureUnion T Λ lmb = m1Part T Λ lmb ∪ specializedTopologyFailureEvent T.verifier.raw lmb := by
  unfold evFailureUnion m1Part
  ext ω; simp only [Finset.mem_union]; tauto

theorem p8Slot_m1Part_B0
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm') (Λ : ℕ) (lmb : K) :
    m1Part (OptimizedFailureEventEv.builtStrategyEv P Qc Qm) Λ lmb =
      m1Part (OptimizedFailureEventEv.builtStrategyEv P Qc' Qm') Λ lmb := by
  obtain ⟨h1, h2⟩ := p8_seed_subevents_B0 P.stateTagChar Λ h
  have h3 := p8_envelope_subevent_B0 P.stateTagChar lmb h
  unfold m1Part OptimizedFailureEventEv.builtStrategyEv
  rw [h1, h2, h3]

/-- **The adaptive form.** -/
theorem p8Slot_m1Part_adaptive {ι : Type}
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    (Qc : ι → Fin P.computeChip.rap.w → F[X]) (Qm : ι → Fin P.memoryChip.rap.w → F[X])
    (hB0 : ∀ χ χ', AgreeB0 P.optimized (Qc χ) (Qc χ') (Qm χ) (Qm χ')) (χ₀ : ι) (Λ : ℕ) (lmb : K) :
    ∀ χ, m1Part (OptimizedFailureEventEv.builtStrategyEv P (Qc χ) (Qm χ)) Λ lmb =
      m1Part (OptimizedFailureEventEv.builtStrategyEv P (Qc χ₀) (Qm χ₀)) Λ lmb :=
  fun χ => p8Slot_m1Part_B0 P (hB0 χ χ₀) Λ lmb

/-- **R1 for summand 11, compiled (`tie11` + `decodedLambdaEventOfEnvs_congr`).** -/
theorem summand11_B0
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hC : AgreeC (P.computeSourceEnv Qc) (P.computeSourceEnv Qc'))
    (hF : ∀ i, ∀ b ∈ lamMemReads, (P.memoryBaseEnv Qm i).trace b = (P.memoryBaseEnv Qm' i).trace b) :
    P.decodedLambdaEventOf Qc Qm = P.decodedLambdaEventOf Qc' Qm' := by
  rw [tie11, tie11]
  exact decodedLambdaEventOfEnvs_congr hC hF _

end Slot

/-! ## 2. The bridge receipts -/
section Recs
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock Nock.Reified Nock.Framework Nock.NockVMROM.Thm54
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage Nock.NockVMROM.Thm54.DeployedStaging
  Nock.NockVMROM.Thm54.RoundFibred Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
  Nock.NockVMROM.Thm54.WalkTilingEvents Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
  Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Polynomial Nock.Walk
noncomputable section

/-! ## 1. Read-set congruences of the production record / label functions (pointwise). -/

section Cong
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Memory record: roles 19..26, 57; base 181. -/
def recordRoles : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 57]
theorem rowRecord_congr' {eK eK' : Env K} {eF eF' : Env F}
    (hK : ∀ r ∈ recordRoles, eK.trace r = eK'.trace r) (hF : eF.trace 181 = eF'.trace 181) :
    OptimizedMemoryHostileAccumulator.rowRecord eK eF = OptimizedMemoryHostileAccumulator.rowRecord eK' eF' := by
  funext c
  unfold OptimizedMemoryHostileAccumulator.rowRecord
  split_ifs with h1 h2
  · have : (c : ℕ) < 8 := h1
    exact hK _ (by unfold recordRoles; interval_cases (c : ℕ) <;> simp)
  · exact hK 57 (by simp [recordRoles])
  · rw [hF]

/-- Memory response terms read the record and `ver` (role 39); `rowResponses` drops the denominator
(role 37, block B2). -/
theorem rowResponses_congr' [DecidableEq K] {eK eK' : Env K} {eF eF' : Env F}
    (hK : ∀ r ∈ recordRoles ++ [39], eK.trace r = eK'.trace r) (hF : eF.trace 181 = eF'.trace 181) :
    OptimizedMemoryHostileAccumulator.rowResponses eK eF = OptimizedMemoryHostileAccumulator.rowResponses eK' eF' := by
  have hr := rowRecord_congr' (fun r hr => hK r (List.mem_append_left _ hr)) hF
  have h39 : eK.trace 39 = eK'.trace 39 := hK 39 (by simp)
  simp only [OptimizedMemoryHostileAccumulator.rowResponses, OptimizedMemoryHostileAccumulator.rowResponseTerms,
    h39, hr]
  split_ifs <;> rfl

/-- Label / child vectors of the memory walk (summands 9, 10): roles 0..14, 45, 46; base 0, 1, 2. -/
def labelRoles : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 45, 46]
def stateBase : List ℕ := [0, 1, 2]

theorem memRowStateOf_congr' [DecidableEq F] {eF eF' : Env F} (hF : ∀ b ∈ stateBase, eF.trace b = eF'.trace b) :
    memRowStateOf eF = memRowStateOf eF' := by
  unfold memRowStateOf
  rw [hF 0 (by simp [stateBase]), hF 1 (by simp [stateBase]), hF 2 (by simp [stateBase])]

theorem memRowLabelVec_congr' [DecidableEq F] {eK eK' : Env K} {eF eF' : Env F}
    (hK : ∀ r ∈ labelRoles, eK.trace r = eK'.trace r) (hF : ∀ b ∈ stateBase, eF.trace b = eF'.trace b) :
    memRowLabelVec eK eF = memRowLabelVec eK' eF' := by
  funext k
  fin_cases k <;> simp only [memRowLabelVec, memRowStateOf_congr' hF] <;>
    exact hK _ (by simp [labelRoles])

theorem memRowChildVec_congr' {eK eK' : Env K} (hK : ∀ r ∈ labelRoles, eK.trace r = eK'.trace r) (j : Fin 2) :
    memRowChildVec eK j = memRowChildVec eK' j := by
  funext k
  fin_cases k <;> fin_cases j <;> simp only [memRowChildVec] <;> exact hK _ (by simp [labelRoles])

variable {M : ℕ} [DecidableEq F]

theorem VCvfo_congr {eK eK' : Fin M → Env K} {eF eF' : Fin M → Env F}
    (hK : ∀ i, ∀ r ∈ labelRoles, (eK i).trace r = (eK' i).trace r)
    (hF : ∀ i, ∀ b ∈ stateBase, (eF i).trace b = (eF' i).trace b) :
    committedMemoryV eK eF = committedMemoryV eK' eF' ∧ committedMemoryCv eK = committedMemoryCv eK' ∧
      foOfMem eF = foOfMem eF' := by
  refine ⟨?_, ?_, ?_⟩
  · funext i; unfold committedMemoryV; split_ifs with h
    · exact memRowLabelVec_congr' (hK _) (hF _)
    · rfl
  · funext i l; unfold committedMemoryCv; split_ifs
    · exact memRowChildVec_congr' (hK _) _
    · rfl
    · rfl
  · funext i; unfold foOfMem; split_ifs with h
    · rw [memRowStateOf_congr' (hF _)]
    · rfl

/-- **Summand 9 is env-local on `labelRoles` / `stateBase`.** -/
theorem summand9_envLocal [Fintype K] [DecidableEq K] (kroots : ℕ) :
    EnvLocal labelRoles stateBase (fun eK eF => memoryPrefixGammaEventOfEnvs (K := K) (F := F) (M := M) eK eF kroots) := by
  intro eK eK' eF eF' hK hF
  obtain ⟨h1, h2, h3⟩ := VCvfo_congr hK hF
  dsimp only; unfold memoryPrefixGammaEventOfEnvs; rw [h1, h2, h3]

/-- **Summand 10 is env-local on the same read set.** -/
theorem summand10_envLocal [Fintype K] [DecidableEq K] (kroots : ℕ) :
    EnvLocal labelRoles stateBase (fun eK eF => memoryForestAlphaEventOfEnvs (K := K) (F := F) (M := M) eK eF kroots) := by
  intro eK eK' eF eF' hK hF
  obtain ⟨h1, h2, h3⟩ := VCvfo_congr hK hF
  dsimp only; unfold memoryForestAlphaEventOfEnvs; rw [h1, h2, h3]

/-- Summand 4's inter records, as a function of the env families (`rfl` to the package's below). -/
def interRecordsOfEnvs [DecidableEq K] (eK : Fin M → Env K) (eF : Fin M → Env F) : FiniteIO.PreChallengeRecords K 10 :=
  ⟨(List.ofFn fun i => if (eF i).trace 2 = 1 then [OptimizedMemoryHostileAccumulator.rowRecord (eK i) (eF i)] else []).flatten,
   (List.ofFn fun i => if (eF i).trace 3 = 1 then [OptimizedMemoryHostileAccumulator.rowRecord (eK i) (eF i)] else []).flatten⟩

def summand4OfEnvs [Fintype K] [DecidableEq K] (eK : Fin M → Env K) (eF : Fin M → Env F) : Finset (K × K) :=
  interFailurePairs (interRecordsOfEnvs eK eF) eK eF

theorem summand4_envLocal [Fintype K] [DecidableEq K] :
    EnvLocal (K := K) (F := F) (M := M) recordRoles [2, 3, 181] summand4OfEnvs := by
  intro eK eK' eF eF' hK hF
  have hr : ∀ i, OptimizedMemoryHostileAccumulator.rowRecord (eK i) (eF i) =
      OptimizedMemoryHostileAccumulator.rowRecord (eK' i) (eF' i) :=
    fun i => rowRecord_congr' (hK i) (hF i 181 (by simp))
  have h2 : ∀ i, (eF i).trace 2 = (eF' i).trace 2 := fun i => hF i 2 (by simp)
  have h3 : ∀ i, (eF i).trace 3 = (eF' i).trace 3 := fun i => hF i 3 (by simp)
  unfold summand4OfEnvs interFailurePairs allRowPoleHitEvent interRecordsOfEnvs
  simp only [hr, h2, h3]

/-- Summand 2's memory half: the response list as a function of the env families. -/
def responsesOfEnvs [DecidableEq K] (eK : Fin M → Env K) (eF : Fin M → Env F) : List (Fin 10 → K) :=
  (List.ofFn fun i => OptimizedMemoryHostileAccumulator.rowResponses (eK i) (eF i)).flatten

theorem summand2mem_envLocal [DecidableEq K] :
    EnvLocal (K := K) (F := F) (M := M) (recordRoles ++ [39]) [181] responsesOfEnvs := by
  intro eK eK' eF eF' hK hF
  unfold responsesOfEnvs
  congr 1; congr 1; funext i
  exact rowResponses_congr' (hK i) (hF i 181 (by simp))

end Cong

/-! ## 2. Ties to the production package (`rfl`). -/

section Ties
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb) (Qm : Fin P.memoryChip.rap.w → F[X])

theorem tie9 : P.memoryPrefixGammaEventOf Qm =
    memoryPrefixGammaEventOfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.kMem := rfl
theorem tie10 : P.memoryForestAlphaEventOf Qm =
    memoryForestAlphaEventOfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.kMem := rfl
theorem tie4 : interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) =
    summand4OfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) := rfl
theorem tie2mem : P.hostileResponses Qm = responsesOfEnvs (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) := rfl
end Ties
end
end Recs

/-! ## 4. -/
section FableB0
open Polynomial

open Nock Nock.Reified Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
section Fable
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

theorem builtSkeleton_computeTree_congr
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm') :
    (OptimizedFailureEventEv.builtSkeletonEv P Qc Qm).computeTree =
      (OptimizedFailureEventEv.builtSkeletonEv P Qc' Qm').computeTree :=
  skeletonEv_computeTree_congr P.stateTagChar h

/-- Summand 13 (root-result pair, coin `z`): B0 only. -/
theorem summand13_B0
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm') :
    OptimizedFailureEventEv.rootResultEv P Qc Qm = OptimizedFailureEventEv.rootResultEv P Qc' Qm' := by
  have hT := builtSkeleton_computeTree_congr P h
  have hclaim : (OptimizedFailureEventEv.builtSkeletonEv P Qc Qm).publicClaim =
      (OptimizedFailureEventEv.builtSkeletonEv P Qc' Qm').publicClaim := by
    unfold SemanticSkeleton.publicClaim; rw [hT]
  unfold OptimizedFailureEventEv.rootResultEv; rw [hclaim]

/-- Summand 12 (request pair, coin `z`): B0 only (memory base `0,1,2,180,181`; the skeleton's
compute tree). -/
theorem summand12_B0
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    {Qc Qc' : Fin P.computeChip.rap.w → F[X]} {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (h : AgreeB0 P.optimized Qc Qc' Qm Qm')
    (hF : ∀ i, ∀ b ∈ PreZComputeCore.Served.preZMemCols,
      (P.memoryBaseEnv Qm i).trace b = (P.memoryBaseEnv Qm' i).trace b) :
    OptimizedFailureEventEv.reqPairEv P Qc Qm = OptimizedFailureEventEv.reqPairEv P Qc' Qm' := by
  have hT := builtSkeleton_computeTree_congr P h
  have hRT : OptimizedFailureEventEv.builtRequestTargets P Qc Qm =
      OptimizedFailureEventEv.builtRequestTargets P Qc' Qm' := by
    have hrows : SemanticStrategy.computeSkeletonRows (OptimizedFailureEventEv.builtSkeletonEv P Qc Qm) =
        SemanticStrategy.computeSkeletonRows (OptimizedFailureEventEv.builtSkeletonEv P Qc' Qm') := by
      unfold SemanticStrategy.computeSkeletonRows; rw [hT]
    unfold OptimizedFailureEventEv.builtRequestTargets
    funext st k
    unfold PreSeedCensus.requestTargets PreSeedCensus.requestList
    rw [hrows]
  have hst : ∀ i, StrategyOfTraces.memoryStateOf (P.memoryBaseEnv Qm i) =
      StrategyOfTraces.memoryStateOf (P.memoryBaseEnv Qm' i) := by
    intro i; unfold StrategyOfTraces.memoryStateOf
    rw [hF i 0 (by decide), hF i 1 (by decide), hF i 2 (by decide)]
  have hlbl : PreSeedCensus.preLblOfEnvs (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos =
      PreSeedCensus.preLblOfEnvs (P.memoryBaseEnv Qm') P.optimized.family.problem.cfg.memRows_pos := by
    funext j; unfold PreSeedCensus.preLblOfEnvs PreSeedCensus.preStateOfEnvs PreSeedCensus.preAtomOfEnvs
    split_ifs
    · rw [hst, hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
    · rw [hst, hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
  have hidx : PreSeedCensus.preReqIdxOfEnvs (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos =
      PreSeedCensus.preReqIdxOfEnvs (P.memoryBaseEnv Qm') P.optimized.family.problem.cfg.memRows_pos := by
    funext j; unfold PreSeedCensus.preReqIdxOfEnvs
    split_ifs
    · rw [hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
    · rw [hF _ _ (by simp [PreZComputeCore.Served.preZMemCols])]
  unfold OptimizedFailureEventEv.reqPairEv PreSeedCensus.reqPairEventOfEnvs PreSeedCensus.reqPairsOfEnvs
    PreSeedCensus.preZNounOfEnvs PreSeedCensus.reqTgtOfEnvs PreSeedCensus.preFoOfEnvs
  rw [hlbl, hidx, hRT]

end Fable
end FableB0



end Nock.NockVMROM.Thm54.PartAB0
