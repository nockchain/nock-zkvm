import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction

/-!
# canonical corrected compute satisfaction

Independent controls for the compute-only forward connective introduced by
`OptimizedComputeSameExecution` and `OptimizedComputeCanonicalSatisfaction`.

Paper frame:
* compute/IO and walk CORE: the paper;
* algorithm and constraints:
  the paper;
* consumed compute side of Theorem 5.4:
  the paper.

-/

namespace Nock.RedTeam.Batch62

open Nock
open Nock.Reified
open Nock.Framework Reify
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeCodec
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable section

/-! ## 1. Exact terminal support -/

set_option maxHeartbeats 8000000 in
theorem terminal_current_ids_exact :
    terminalCurrentExtGateIds.length = 75 ∧
    terminalCurrentExtGateIds.Nodup := by
  constructor
  · exact terminalCurrentExtGateIds_length
  · decide

set_option maxHeartbeats 8000000 in
theorem terminal_suppressed_ids_exact :
    (List.ofFn fun i : CorrectedCoreExtGateId => i).filter
        (fun i => i ∉ terminalCurrentExtGateIds) =
      [packedLnChainId, packedWalkLnId, packedWalkCountId, packedWalkAccId,
        packedQueueNonEmptyId, packedQueueTilingId, packedChainId] := by
  decide

/-- On a last row, precisely the five omitted transition/residual positions are
annihilated without reading any successor. -/
theorem terminal_suppressed_semantics_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (hlast : env.baseTrace 12 = 1) :
    ∀ i ∈ ([packedLnChainId, packedWalkLnId, packedWalkCountId, packedWalkAccId,
        packedChainId] : List CorrectedCoreExtGateId),
      correctedCoreSemanticValue env i = 0 := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have hnl : notLastScalar env = 0 := by simp [notLastScalar, hlast]
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId,
      packedChainId, packedLnChainId, packedWalkLnId, ↓reduceIte]
    rw [hnl]; simp
  · simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId,
      packedChainId, packedLnChainId, packedWalkLnId, ↓reduceIte]
    rw [hnl]; simp
  · simp only [correctedCoreSemanticValue, packedWalkCountId, ↓reduceIte]
    rw [hnl]; simp
  · simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId,
      ↓reduceIte]
    rw [hnl]; simp
  · simp only [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId,
      packedChainId, ↓reduceIte]
    simp [accAfterChain, CorrectedFinalTypedExpr.eval, hlast]

/-- Every retained terminal ID is the direct production gate, while only the
five complementary IDs are suppressed. -/
theorem terminal_retained_semantics_are_direct
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) :
    ∀ i ∈ terminalCurrentExtGateIds,
      correctedCoreSemanticValue env i = (correctedFinalExtGate i).eval env := by
  intro i hi
  have h : i ≠ packedLnChainId ∧ i ≠ packedWalkLnId ∧ i ≠ packedWalkCountId ∧
      i ≠ packedWalkAccId ∧ i ≠ packedChainId := by
    have hv : (i : ℕ) < 72 ∨ (i : ℕ) = 78 ∨ (i : ℕ) = 79 ∨ (i : ℕ) = 80 := by
      simp only [terminalCurrentExtGateIds, List.mem_append] at hi
      rcases hi with h | h
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
        exact Or.inl j.isLt
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h78 | h79 | h80
        · exact Or.inr (Or.inl (congrArg Fin.val h78))
        · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h79)))
        · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val h80)))
    constructor
    · intro h; have := congrArg Fin.val h; simp [packedLnChainId] at this; omega
    constructor
    · intro h; have := congrArg Fin.val h; simp [packedWalkLnId] at this; omega
    constructor
    · intro h; have := congrArg Fin.val h; simp [packedWalkCountId] at this; omega
    constructor
    · intro h; have := congrArg Fin.val h; simp [packedWalkAccId] at this; omega
    · intro h; have := congrArg Fin.val h; simp [packedChainId] at this; omega
  have h89 : ¬ (i = packedLnChainId ∨ i = packedWalkLnId) := fun h' => h'.elim h.1 h.2.1
  simp only [correctedCoreSemanticValue, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h89, ↓reduceIte]

theorem terminal_has_no_fabricated_successor
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {R : PlusIOSegmentedFamily F K} (hn : 0 < R.problem.cfg.compRows) :
    ¬ (((⟨R.problem.cfg.compRows - 1, Nat.sub_lt hn (by omega)⟩ :
        Fin R.problem.cfg.compRows) : ℕ) + 1 < R.problem.cfg.compRows) := by
  change ¬ R.problem.cfg.compRows - 1 + 1 < R.problem.cfg.compRows
  rw [Nat.sub_add_cancel hn]
  exact Nat.lt_irrefl _

/-! ## 2. The 94-column structural decoder -/

/-- The eight source blocks are exhaustive and pairwise exclusive, including
all seven boundary cuts. -/
theorem decoder_block_partition_unique (j : Fin 94) :
    [decide ((j : ℕ) < 11),
      decide (11 ≤ (j : ℕ) ∧ (j : ℕ) < 47),
      decide (47 ≤ (j : ℕ) ∧ (j : ℕ) < 65),
      decide (65 ≤ (j : ℕ) ∧ (j : ℕ) < 67),
      decide (67 ≤ (j : ℕ) ∧ (j : ℕ) < 75),
      decide (75 ≤ (j : ℕ) ∧ (j : ℕ) < 83),
      decide (83 ≤ (j : ℕ) ∧ (j : ℕ) < 91),
      decide (91 ≤ (j : ℕ) ∧ (j : ℕ) < 94)].count true = 1 := by
  fin_cases j <;> decide

theorem decoder_block_widths :
    11 + (47 - 11) + (65 - 47) + (67 - 65) +
      (75 - 67) + (83 - 75) + (91 - 83) + (94 - 91) = 94 := by
  norm_num

set_option maxRecDepth 300000 in
/-- Current table decoding cannot reach corrected residual roles 58--60, walk
role 61, or a non-table challenge. -/
theorem current_decoder_reserved_roles_and_challenges_unreachable :
    ∀ i : Fin 94,
      (∀ j ∈ ([71, 72, 73, 74] : List ℕ),
        (.traceCur, j) ∉ (computeTraceSubst .traceCur i).vars) ∧
      (∀ q ∈ ([6, 7, 8, 9, 10, 11] : List ℕ),
        (.challenge, q) ∉ (computeTraceSubst .traceCur i).vars) := by
  intro i
  fin_cases i <;> decide

/-- Independent same-object restatement of the complete current decoder.  It
uses the same assignment, obligation proof, row, records, coins, and auxiliary
witness on both sides. -/
theorem decoder_all_94_same_object
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows) (j : Fin 94) :
    (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
      (computeEnvFull R.problem.cfg.challenges.computeInputs
        (ComputeTable.opSel (R.problem.exec.computePubAt i).state)
        (R.problem.exec.computePubAt i)
        (R.problem.exec.computeDecAt i)
        (A.exact.computeTableAux i)).trace j :=
  exactFinalCurrentEnv_table_current A hA i j j.isLt

/-- OP0, OP1, OP6, and OP9 all pass through the same total decoder theorem;
no opcode-specific fallback environment is introduced. -/
theorem decoder_selected_states_same_object
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (i : Fin R.problem.cfg.compRows)
    (_hs : (R.problem.exec.computePubAt i).state = ComputeTable.State.s0 ∨
      (R.problem.exec.computePubAt i).state = ComputeTable.State.s1 ∨
      (R.problem.exec.computePubAt i).state = ComputeTable.State.s6 ∨
      (R.problem.exec.computePubAt i).state = ComputeTable.State.s9) :
    ∀ j : Fin 94,
      (Env.ofSubst computeSubst (exactFinalCurrentEnv A i).toSourceEnv).trace j =
        (computeEnvFull R.problem.cfg.challenges.computeInputs
          (ComputeTable.opSel (R.problem.exec.computePubAt i).state)
          (R.problem.exec.computePubAt i)
          (R.problem.exec.computeDecAt i)
          (A.exact.computeTableAux i)).trace j := by
  intro j
  exact decoder_all_94_same_object A hA i j

/-! ## 3. Same-object capstone shape -/

theorem forward_capstone_threads_one_object
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [DecidableEq F] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K} [FiniteDimensional F K]
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
    (hpub : ExactFinalPublicCoordinates b R hn pubVal)
    (hreq : ExactFinalRequestsCoordinate b A pubVal)
    (hln : ExactFinalLineOrigin R hn)
    (hord : 2 ≤ R.problem.cfg.compRows →
      R.problem.cfg.compRows ≤ orderOf R.computeWalkAlpha)
    (hax : FormRAxisBound A b)
    (hbasis : FormRBasis b)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit) :=
  correctedCanonicalFinalTrace_satisfies
    A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hpub hreq hln hord
    hax hbasis hwidth

/-! ## 4. Concrete singleton F73/K73cubic satisfaction -/

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

abbrev concreteA := OptimizedComputeSampledTrace.Concrete.honestSampled

theorem concrete_compRows_eq_one :
    honestLegacyFamily.problem.cfg.compRows = 1 := by
  rfl

def concreteNodes : Fin honestLegacyFamily.problem.cfg.compRows → F73 :=
  fun _ => 1

theorem concreteNodes_injective : Function.Injective concreteNodes := by
  intro i j _
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hi' : (i : ℕ) < 1 := by
    simpa only [concrete_compRows_eq_one] using hi
  have hj' : (j : ℕ) < 1 := by
    simpa only [concrete_compRows_eq_one] using hj
  omega

def concreteChallengeCoordinates (i : ℕ) : F73 :=
  if hi : i < 36 then
    coord basis73
      (exactFinalChallenge concreteA (i / 3))
      ⟨i % 3, Nat.mod_lt _ (by omega)⟩
  else 0

theorem concreteChallengeCoordinates_exact :
    ExactFinalChallengeCoordinates basis73 concreteA concreteChallengeCoordinates := by
  intro q k
  rw [concreteChallengeCoordinates, dif_pos (by omega)]
  have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
  have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
  rw [hdiv]
  congr 1
  apply Fin.ext
  exact hmod

def concretePublicCoordinates (i : ℕ) : F73 :=
  if hi : i < 6 then
    coord basis73
      (if i / 3 = 0 then honestLegacyFamily.computeWalkAlpha
        else honestLegacyFamily.computeWalkSeed)
      ⟨i % 3, Nat.mod_lt _ (by omega)⟩
  else if h9 : 6 ≤ i ∧ i < 9 then
    -- `requests`: the sampled IO terminal
    coord basis73 concreteA.witness10.terminal ⟨i - 6, by omega⟩
  else if hfirst : 20 ≤ i ∧ i < 31 then
    if i - 20 = stateIndex
        (honestLegacyFamily.problem.exec.computePubAt
          ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state then 1 else 0
  else if hlast : 31 ≤ i ∧ i < 42 then
    if i - 31 = stateIndex
        (honestLegacyFamily.problem.exec.computePubAt
          ⟨honestLegacyFamily.problem.cfg.compRows - 1,
            Nat.sub_lt honestLegacyFamily.problem.cfg.compRows_pos (by omega)⟩).state
      then 1 else 0
  else 0

theorem concreteRequests_exact :
    ExactFinalRequestsCoordinate basis73 concreteA concretePublicCoordinates := by
  intro k
  have hk := k.isLt
  rw [concretePublicCoordinates, dif_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- F73's honest first compute row has `ln_prev = 1` (`ConcreteStrictPackage.computePub`) — the
origin the W6.1 stage-2A gate `finalLnInit` pins. -/
theorem concreteLineOrigin :
    ExactFinalLineOrigin honestLegacyFamily honestLegacyFamily.problem.cfg.compRows_pos := by
  show (honestLegacyFamily.problem.exec.computePubAt ⟨0, _⟩).ln_prev = 1
  have hij : (⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩ :
      Fin honestLegacyFamily.problem.cfg.compRows) =
      OptimizedComputeSampledTrace.Concrete.honestRowIndex := Fin.ext rfl
  rw [hij, OptimizedComputeSampledTrace.Concrete.honest_computePubAt]
  rfl

theorem concretePublicCoordinates_exact :
    ExactFinalPublicCoordinates basis73 honestLegacyFamily
      honestLegacyFamily.problem.cfg.compRows_pos concretePublicCoordinates := by
  constructor
  · intro q k
    rw [concretePublicCoordinates, dif_pos (by omega)]
    have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
    have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    by_cases hq : q = 0
    · subst q
      simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      congr 1
      apply Fin.ext
      exact hmod
    · have hqnat : (q : ℕ) ≠ 0 := by
        intro hv
        apply hq
        apply Fin.ext
        exact hv
      simp only [hqnat, ↓reduceIte, hq]
      congr 1
      apply Fin.ext
      exact hmod
  constructor
  · intro j
    rw [concretePublicCoordinates, dif_neg (by omega), dif_neg (by omega),
      dif_pos (by omega)]
    by_cases hs : j = stateIndex
        (honestLegacyFamily.problem.exec.computePubAt
          ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state
    · simp [hs]
    · have hv : (j : ℕ) ≠
          (stateIndex (honestLegacyFamily.problem.exec.computePubAt
            ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state : ℕ) :=
        fun h => hs (Fin.ext h)
      simp [hs, hv]
  · intro j
    rw [concretePublicCoordinates, dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_pos (by omega)]
    by_cases hs : j = stateIndex
        (honestLegacyFamily.problem.exec.computePubAt
          ⟨honestLegacyFamily.problem.cfg.compRows - 1,
            Nat.sub_lt honestLegacyFamily.problem.cfg.compRows_pos (by omega)⟩).state
    · simp [hs]
    · have hv : (j : ℕ) ≠
          (stateIndex (honestLegacyFamily.problem.exec.computePubAt
            ⟨honestLegacyFamily.problem.cfg.compRows - 1,
              Nat.sub_lt honestLegacyFamily.problem.cfg.compRows_pos (by omega)⟩).state : ℕ) :=
        fun h => hs (Fin.ext h)
      simp [hs, hv]

theorem concrete_orbit_step_vacuous :
    ∀ (i : Fin honestLegacyFamily.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < honestLegacyFamily.problem.cfg.compRows),
      concreteNodes ⟨(i : ℕ) + 1, hi⟩ = strictOrbit.ω * concreteNodes i := by
  intro i hi
  have hi' : (i : ℕ) + 1 < 1 := by
    simpa only [concrete_compRows_eq_one] using hi
  omega

theorem concreteFormRWidth : FormRWidth F73 := by
  have hc : ringChar F73 = 73 := ZMod.ringChar_zmod_n 73
  constructor
  · change Nat.size (ringChar F73) ≤ 64
    rw [hc]; decide
  · change 0 < Nat.size (ringChar F73) ∧ 3 < ringChar F73
    rw [hc]; decide

/-- Honest F73 row is `.s1`; no committed axis leaf. -/
theorem concreteFormRAxisBound : FormRAxisBound concreteA basis73 := by
  intro i L hL
  have hdec :
      OptimizedComputeCodec.decodeState (encodedRowAt concreteA i).base =
        (honestLegacyFamily.problem.exec.computePubAt i).state := by
    simp [encodedRowAt, OptimizedComputeOverlay.sampledEncode,
      OptimizedComputeCodec.decodeState_encodeBase]
  have hst : (honestLegacyFamily.problem.exec.computePubAt i).state = .s1 := by
    have hij : i = OptimizedComputeSampledTrace.Concrete.honestRowIndex := by
      apply Fin.ext
      have hi : (i : ℕ) < 1 := by
        simpa [concrete_compRows_eq_one] using i.isLt
      simp [OptimizedComputeSampledTrace.Concrete.honestRowIndex]
      omega
    rw [hij, OptimizedComputeSampledTrace.Concrete.honest_computePubAt]
    rfl
  simp [axisLeafCoord, hdec, hst] at hL

theorem concrete_correctedCanonicalFinalTrace_satisfies
    (hbasis : FormRBasis basis73) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP honestLegacyFamily.problem.cfg.compRows_pos
        concreteNodes basis73 concreteChallengeCoordinates concretePublicCoordinates
        strictOrbit)
      (correctedCanonicalFinalTrace concreteA
        honestLegacyFamily.problem.cfg.compRows_pos concreteNodes basis73
        concreteChallengeCoordinates concretePublicCoordinates strictOrbit) := by
  exact correctedCanonicalFinalTrace_satisfies
    concreteA OptimizedComputeSampledTrace.Concrete.honest_obligations
    honestLegacyFamily.problem.cfg.compRows_pos
    concreteNodes concreteNodes_injective basis73
    concreteChallengeCoordinates concretePublicCoordinates strictOrbit
    concrete_orbit_step_vacuous
    concreteChallengeCoordinates_exact concretePublicCoordinates_exact concreteRequests_exact
    concreteLineOrigin
    (fun h => by
      have := concrete_compRows_eq_one
      omega)
    concreteFormRAxisBound hbasis concreteFormRWidth

/-! ## 5. Malformed discrimination -/

abbrev F73rt := ZMod 73

def malformedTerminalTableEnv : Env F73rt where
  trace i := if i = 0 then 2 else if i = 12 then 1 else 0
  traceNext _ := 0
  chal _ := 0
  pub _ := 0

theorem malformed_terminal_current_table_value_rejected :
    (selectorBool 0).eval malformedTerminalTableEnv ≠ 0 ∧
      selectorBool 0 ∈
        correctedFinalComputeAllGates (F := F73rt) (K := K73cubic) 1 basis73 := by
  constructor
  · norm_num [selectorBool, bv, malformedTerminalTableEnv,
      CoordinateCompiler.CoeffExpr.eval]
    decide
  · rw [correctedFinalComputeAllGates]
    simp only [List.mem_append]
    have hbase : selectorBool 0 ∈ finalBaseTransitionGates (F := F73rt) 1 := by
      rw [finalBaseTransitionGates]
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      exact ⟨0, by simp, rfl⟩
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hbase)))))))

theorem malformed_sampled_denom_inverse_rejected
    {K : Type} [Field K] (coins : FiniteIO.IOCoins K) (v : Fin 9 → K)
    (hden : FiniteIO.compress coins v ≠ 0) :
    FiniteIO.compress coins v * 0 ≠ 1 := by
  exact ComputeSampledIO.wrong_inverse_rejected coins v 0 hden
    (by simpa [ComputeSampledIO.requestInv] using (inv_ne_zero hden).symm)

def concreteMalformedDenomCoins : FiniteIO.IOCoins F73rt where
  gamma := 0
  pole := 1

def concreteMalformedDenomRecord : Fin 9 → F73rt := fun _ => 0

theorem concrete_malformed_sampled_denom_inverse_rejected :
    FiniteIO.compress concreteMalformedDenomCoins concreteMalformedDenomRecord * 0 ≠ 1 := by
  apply malformed_sampled_denom_inverse_rejected
  simp [FiniteIO.compress, Walk.rlc, concreteMalformedDenomCoins,
    concreteMalformedDenomRecord]

def malformedSelectorPublicEnv : Env F73rt where
  trace i := if i = 0 ∨ i = 11 then 1 else 0
  traceNext _ := 0
  chal i := if i = finalScalarChallengeBase then 0 else 0
  pub _ := 0

theorem malformed_selector_public_rejected :
    ((CoordinateCompiler.CoeffExpr.mul isFirstVar
      (finalSelectorPublicCheck .traceCur 20)).eval malformedSelectorPublicEnv) ≠ 0 := by
  norm_num [finalSelectorPublicCheck, CoeffExpr.sumList,
    isFirstVar, bv, malformedSelectorPublicEnv, finalScalarChallengeBase,
    List.range, List.range.loop, CoordinateCompiler.CoeffExpr.eval]

def shiftedChallengeCoordinates (i : ℕ) : F73 :=
  if i = 0 then concreteChallengeCoordinates i + 1
  else concreteChallengeCoordinates i

theorem shifted_challenge_mapping_rejected :
    ¬ ExactFinalChallengeCoordinates basis73 concreteA shiftedChallengeCoordinates := by
  intro h
  have hbad := h 0 0
  have hgood := concreteChallengeCoordinates_exact 0 0
  have hbad' :
      concreteChallengeCoordinates 0 + 1 =
        coord basis73 (exactFinalChallenge concreteA 0) 0 := by
    simpa [shiftedChallengeCoordinates] using hbad
  have hgood' :
      concreteChallengeCoordinates 0 =
        coord basis73 (exactFinalChallenge concreteA 0) 0 := by
    simpa using hgood
  have heq : concreteChallengeCoordinates 0 + 1 =
      concreteChallengeCoordinates 0 := hbad'.trans hgood'.symm
  have hone : (1 : F73) = 0 := by
    calc
      1 = (concreteChallengeCoordinates 0 + 1) -
          concreteChallengeCoordinates 0 := by ring
      _ = concreteChallengeCoordinates 0 -
          concreteChallengeCoordinates 0 := by rw [heq]
      _ = 0 := sub_self _
  exact one_ne_zero hone

def shiftedSelectorPublicCoordinates (i : ℕ) : F73 :=
  if i = 20 + (stateIndex
      (honestLegacyFamily.problem.exec.computePubAt
        ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state : ℕ) then
    concretePublicCoordinates i + 1
  else concretePublicCoordinates i

theorem shifted_selector_public_mapping_rejected :
    ¬ ExactFinalPublicCoordinates basis73 honestLegacyFamily
      honestLegacyFamily.problem.cfg.compRows_pos shiftedSelectorPublicCoordinates := by
  intro h
  let j := stateIndex
    (honestLegacyFamily.problem.exec.computePubAt
      ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state
  have hbad := h.2.1 j
  have hgood := concretePublicCoordinates_exact.2.1 j
  have hidx : 20 + (j : ℕ) =
      20 + (stateIndex (honestLegacyFamily.problem.exec.computePubAt
        ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state : ℕ) := rfl
  have hbad' :
      concretePublicCoordinates (20 + (j : ℕ)) + 1 =
        (if j = stateIndex
            (honestLegacyFamily.problem.exec.computePubAt
              ⟨0, honestLegacyFamily.problem.cfg.compRows_pos⟩).state then 1 else 0) := by
    simpa [shiftedSelectorPublicCoordinates, hidx] using hbad
  have heq : concretePublicCoordinates (20 + (j : ℕ)) + 1 =
      concretePublicCoordinates (20 + (j : ℕ)) := by
    exact hbad'.trans hgood.symm
  have hone : (1 : F73) = 0 := by
    calc
      1 = (concretePublicCoordinates (20 + (j : ℕ)) + 1) -
          concretePublicCoordinates (20 + (j : ℕ)) := by ring
      _ = concretePublicCoordinates (20 + (j : ℕ)) -
          concretePublicCoordinates (20 + (j : ℕ)) := by rw [heq]
      _ = 0 := sub_self _
  exact one_ne_zero hone


theorem malformed_residual_auxiliary_rejected
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w →
      Polynomial F)
    (x : F) (hx : x ∈ rowNodeSet nodes)
    (j : CorrectedResidualWitnessId) (k : Fin 3)
    (hbad : (correctedAuxCoord b j k).eval
      (envOfTrace P orbit.ω x chalVal pubVal) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P := by
  apply production_not_satisfies_of_gate_nonzero
    hn nodes b chalVal pubVal orbit P x hx (correctedAuxCoord b j k)
  · have haux : correctedAuxCoord b j k ∈ correctedAux b := by
      rw [correctedAux]
      apply List.mem_flatten.mpr
      exact ⟨List.ofFn (fun q : Fin 3 => correctedAuxCoord b j q),
        List.mem_ofFn.mpr ⟨j, rfl⟩,
        List.mem_ofFn.mpr ⟨k, rfl⟩⟩
    rw [correctedFinalComputeAllGates]
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr haux))))))
  · exact hbad

/-- A changed first/last mask is rejected by preprocessing equality before any
semantic gate can hide it. -/
theorem malformed_fixed_mask_rejected
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w →
      Polynomial F)
    (j : Fin (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).fixedCount)
    (hwrong :
      P ((ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).preprocessingColumn j) ≠
        (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).preprocessing j) :
    ¬ RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit) P :=
  production_wrong_preprocessing_rejected
    hn nodes b chalVal pubVal orbit P j hwrong

/-! ## 6. Exact resource and scope controls -/

theorem exact_bucket_and_resource_census
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) :
    let Q := ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit
    (finalBaseTransitionGates (F := F) n).length = 15 ∧
      correctedLoweredExt.length = 82 ∧
      Fintype.card CorrectedResidualWitnessId = 3 ∧
      correctedEndpoint2.length = 6 ∧ correctedEndpoint4.length = 1 ∧
      (finalEndpointEqualityChecks (F := F)).length = 22 ∧
      Q.fixedCount = 2 ∧ Q.rap.e = 3 ∧ Q.rap.k = 2 ∧
      Q.rap.wRAP = ![297, 6] ∧ Q.rap.w = 303 ∧
      Q.rap.s = 418 ∧ Q.rap.d = 4 := by
  exact ⟨finalBaseTransitionGates_length n, corrected_lowered_counts.1,
    by decide, corrected_lowered_counts.2.1, corrected_lowered_counts.2.2,
    rfl, rfl, rfl, rfl, rfl, rfl, correctedFinalComputeAllGates_length n b, rfl⟩

set_option maxRecDepth 300000 in
theorem all_production_extension_sources_lower_without_fallback :
    correctedLoweredExt.length = finalExtTransitionGates.length := by
  rw [corrected_lowered_counts.1, finalExtTransitionGates_length]

set_option maxHeartbeats 8000000 in
theorem production_nonio_source_equations_nodup :
    finalNonIOSourceFamilies17.flatten.Nodup := by
  set_option maxRecDepth 300000 in
    decide

set_option maxHeartbeats 8000000 in
theorem production_extension_gate_bodies_nodup :
    finalExtTransitionGates.Nodup := by
  set_option maxRecDepth 300000 in
    decide

/-- These are the only primitive trace indices emitted by the corrected typed
compiler; recursive constructors only combine their subexpressions. -/
theorem corrected_compiler_primitive_trace_indices_in_width :
    (∀ i : Fin 13, (i : ℕ) < 202) ∧
      (∀ (i : Fin 63) (k : Fin 3), correctedFinalExtCoordIndex i k < 202) := by
  constructor
  · intro i
    omega
  · intro i k
    simp only [correctedFinalExtCoordIndex]
    omega

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem production_extension_sources_are_not_literal_zero :
    ∀ g ∈ finalExtTransitionGates, g ≠ (.Const 0 : Expr) := by
  intro g hg
  have hall : ∀ g ∈ finalExtTransitionGates, g ≠ (.Const 0 : Expr) := by decide
  exact hall g hg


theorem reverse_scope_remains_collision_conditioned
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {n : ℕ} {env : CorrectedFinalTypedEnv F K} {envF : Env F}
    (hsource : CorrectedComputeSourceObligations n env envF)
    (hnotLast : env.baseTrace 12 = 0) :
    CorrectedDecodedTransitionSources env :=
  corrected_conditional_transition_soundness hsource hnotLast

theorem paper_alias_unchanged :
    @«Thm:NockVMROM:forest-control» = @Nock.NockVM.V_NockVMROM_forest :=
  rfl

#print axioms terminal_current_ids_exact
#print axioms terminal_suppressed_semantics_zero
#print axioms decoder_block_partition_unique
#print axioms current_decoder_reserved_roles_and_challenges_unreachable
#print axioms decoder_all_94_same_object
#print axioms forward_capstone_threads_one_object
#print axioms concrete_correctedCanonicalFinalTrace_satisfies
#print axioms malformed_terminal_current_table_value_rejected
#print axioms malformed_sampled_denom_inverse_rejected
#print axioms concrete_malformed_sampled_denom_inverse_rejected
#print axioms malformed_selector_public_rejected
#print axioms shifted_challenge_mapping_rejected
#print axioms shifted_selector_public_mapping_rejected
#print axioms malformed_residual_auxiliary_rejected
#print axioms malformed_fixed_mask_rejected
#print axioms exact_bucket_and_resource_census
#print axioms production_extension_gate_bodies_nodup
#print axioms corrected_compiler_primitive_trace_indices_in_width
#print axioms production_extension_sources_are_not_literal_zero
#print axioms reverse_scope_remains_collision_conditioned
#print axioms paper_alias_unchanged

end
end Nock.RedTeam.Batch62
