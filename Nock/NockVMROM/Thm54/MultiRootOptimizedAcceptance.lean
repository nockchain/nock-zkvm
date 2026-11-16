import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The accepted optimized chip-level tuple at the phase-correct package

Three of the fourteen conjuncts of `OptimizedFullStrictThm54Statement` quantify over the
*optimized chip-level* acceptance predicate `OptimizedHistoricalAcceptanceAt Qc Qm c`
: `acceptance_to_target`, `complete_false_acceptance_bound` and
`complete_false_acceptance_bits`.  Outside the hand-built F73 fixture no accepted optimized tuple
had been exhibited, so at every *constructed* package those three conjuncts carried no witness.

This module exhibits one at `MultiRootPhaseCorrect.packageP` — the phase-correct package over the
nonterminal two-serviced-root execution, whose arithmetization *and* commitment halves are both
produced by the generic constructors.

What connects the two layers is not new mathematics.  `OptimizedHistoricalAcceptanceAt` factors as
P8 acceptance, the whole-problem `same_problem` link, and a trace side that is entirely about the
package's *own* canonical `199/98` and `196/104` traces (`optimizedHistoricalAcceptanceAt_iff`).
The P8 half is `MultiRootPhaseCorrect.packageP_accepts`; the `same_problem` half is the package's
`honest_specialization` field, because `coinN a g` samples exactly `(servedSeed, fixtureAlpha)`; and
the trace half is discharged by the canonical traces the package already carries, with all eight
sampled challenge coordinates read off those traces (every one of the challenge fields is `rfl`,
because `envOfTrace` puts the challenge map in a slot no row index touches).

The one genuinely new ingredient is `canonical_nonterminal_nonIO_source_zero`: the generic form of
`OptimizedStrictNonterminalConcrete.canonical_row0_nonIO_source_zero`. This fixture has two compute rows, and row `0` has a successor,
so `exact_correctedDecodedTransitionSources` applies and all `511` non-IO sources genuinely vanish.

The terminal *selector* check is the other place where two rows differ from one: the released
`computeScalarEnv` is pinned at row `0`, whereas the committed public block at offset `31` carries
the *last* row's one-hot state.  Here the first row is `parentPubS` with state `s4` and the last is
`servedPub` with state `s0`, so the head of the terminal selector error list is `-1`, and the
committed scalar challenge `0` is not a root of that RLC.  That is a real, computed exclusion, not
an all-zero one.

Optimized acceptance
pins the sampled seed and `alphaM` to the committed fibre, because `OptimizedSameProblemAt` is a
field of the acceptance record; `ProductionStrategy.Accepts` has no such field, so the earlier
reduction does not transfer. What does move is the census: all fourteen committed comparison pairs
are self-comparisons, so `SepSeed` holds at *every* seed and the collision failure event is empty
outright; and the committed skeleton's only size-window noun is the atom `resultS`, so the
size-window event is exactly the low-multiplicative-order-seed event. Emptiness of the P8
false-acceptance set therefore now waits on three named exclusions at accepted coins — specialized
topology, guarded axis, low-order seed — a premise set strictly weaker than the earlier single
fibre-pinning hypothesis. None of the three is discharged here, and the two `p8_fixed_field_*`
conjuncts stay unclassified. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

open scoped Classical Polynomial
open Nock Nock.Framework Nock.Reified Nock.NockVMROM
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeOverlay
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.StrictExtension
open Module
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootHonestArrays
open Nock.NockVMROM.Thm54.MultiRootNonzeroChallenges
open Nock.NockVMROM.Thm54.MultiRootPhaseCorrect
open Nock.NockVMROM.Thm54.BuildableChips

noncomputable section

-- 28th: the generic canonical-trace section (`specializedProblem_congr` …
-- `canonical_memory_outside_failure`) is hoisted verbatim to `OptimizedCanonicalTraces` (core).

/-! ## The nonterminal canonical row decodes all 511 non-IO sources

`canonical_terminal_finalComputeCollisionFree` covers the last compiled row only, because four of
the seventeen families are successor families and are singletons there.  A nonterminal row has a
successor, so `exact_correctedDecodedTransitionSources` applies and *every* source vanishes.  This
is the generic form of `OptimizedStrictNonterminalConcrete.canonical_row0_nonIO_source_zero`
. -/

section Nonterminal

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

set_option maxRecDepth 300000 in

theorem canonical_nonterminal_nonIO_source_zero
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
    (i : Fin R.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.compRows)
    (e : Expr) (he : e ∈ finalNonIOSourceFamilies17.flatten) :
    e.eval
      (gatherCorrectedFinalTypedEnv b
        (envOfTrace
          (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
          orbit.ω (nodes i) chalVal pubVal)).toSourceEnv = 0 := by
  let can := gatherCorrectedFinalTypedEnv b
    (envOfTrace
      (correctedCanonicalFinalTrace A hn nodes b chalVal pubVal orbit)
      orbit.ω (nodes i) chalVal pubVal)
  let ex := exactFinalTransitionEnv A i hi
  let exPub : CorrectedFinalTypedEnv F K :=
    { ex with extensionPublic := can.extensionPublic
              scalarPublic := can.scalarPublic }
  obtain ⟨t, htLower, htResidual, htPublic⟩ :=
    OptimizedStrictNonterminalConcrete.nonterminalSource97_lower_receipt e he
  rw [correctedLowerFinal_eval can e t htLower]
  have hsame : t.eval can = t.eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_residualFree
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv] using
        canonical_gather_base_current A hn nodes hnodes b chalVal pubVal orbit i q
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv] using
        canonical_gather_base_next A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) q
    · intro role hrole
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core A hn nodes hnodes b chalVal pubVal orbit i r
        have hex : exPub.extTrace role =
            coreExtensionValue (encodedRowAt A i) r := by
          simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTrace role = coreExtensionValue (encodedRowAt A i) r := by
          simpa [can, r, formRLeafCore] using hc
        exact hc'.trans hex.symm
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow] using
          canonical_gather_walkLine A hn nodes hnodes b chalVal pubVal orbit i
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow] using
          canonical_gather_walkInv A hn nodes hnodes b chalVal pubVal orbit i
    · intro role hrole
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core_next A hn nodes hnodes b chalVal pubVal orbit i hi
          (by simpa [mul_comm] using hstep i hi) r
        have hex : exPub.extTraceNext role =
            coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) r := by
          simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r]
        have hc' : can.extTraceNext role =
            coreExtensionValue (encodedRowAt A ⟨(i : ℕ) + 1, hi⟩) r := by
          simpa [can, r, formRLeafCore] using hc
        exact hc'.trans hex.symm
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          Nat.add_assoc] using
            canonical_gather_walkLine_next A hn nodes hnodes b chalVal pubVal orbit i hi
              (by simpa [mul_comm] using hstep i hi)
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          Nat.add_assoc] using
            canonical_gather_walkInv_next A hn nodes hnodes b chalVal pubVal orbit i hi
              (by simpa [mul_comm] using hstep i hi)
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv] using
        canonical_gather_challenge A hn nodes b chalVal pubVal orbit hchal i q
    · intro q; rfl
    · intro q; rfl
    · exact htResidual
  have hpub : t.eval exPub = t.eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact htPublic
    · intro q; rfl
    · intro q; rfl
    · rfl
  have hex : t.eval ex = 0 := by
    rw [← correctedLowerFinal_eval ex e t htLower]
    exact exact_finalNonIOSourceFamilies17 A hA i hi e he
  rw [hsame, hpub, hex]

end Nonterminal

/-! ## The compute half of the optimized failure event, at the canonical trace -/

section ComputeExclusion

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]
variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)


theorem canonical_row_collisionFree (i : Fin P.optimized.family.problem.cfg.compRows) :
    FinalComputeCollisionFree (P.computeSourceEnv (canonicalComputeTrace P) i) := by
  by_cases hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows
  · intro es hes _ e he
    exact canonical_nonterminal_nonIO_source_zero P.optimized.sampled
      P.optimized.computeObligations P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.computeNodes_injective P.optimized.basis
      P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit
      P.optimized.computeAdjacentOrbit P.optimized.computeChallengePins i hi e
      (List.mem_flatten.mpr ⟨es, hes, he⟩)
  · have hlast : i = ⟨P.optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos Nat.one_pos⟩ := by
      apply Fin.ext
      have hil := i.isLt
      simp only
      omega
    rw [hlast]
    exact canonical_terminal_finalComputeCollisionFree P.optimized.sampled
      P.optimized.computeObligations P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.computeNodes_injective P.optimized.basis
      P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit
      P.optimized.computeChallengePins

/-- Vacuous since W3 stage 2: the tuple is a unit.  Previously stated as the two field
equalities. -/
theorem canonical_challenge9_good :
    True :=
  trivial

theorem canonical_challenge11_good :
    True :=
  trivial

theorem canonical_walkInit_zero :
    ∀ a ∈ walkInitErrors (P.computeWalkEnv (canonicalComputeTrace P)), a = 0 := by
  have hwalkSource := canonical_masked_walk_init_sources P.optimized.sampled
    P.optimized.computeObligations P.optimized.family.problem.cfg.compRows_pos
    P.optimized.computeNodes P.optimized.computeNodes_injective P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit
    P.optimized.computeChallengePins P.optimized.computePublicPins
  intro a ha
  simp only [walkInitErrors, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact hwalkSource.1
  · exact hwalkSource.2

/-- The eleven scalar selector columns of the canonical trace are the *first* compiled row's
one-hot state vector: `computeScalarEnv` is pinned at row `0`. -/
theorem canonical_scalarEnv_trace (j : Fin 11) :
    (P.computeScalarEnv (canonicalComputeTrace P)).trace (j : ℕ) =
      if j = OptimizedComputeCodec.stateIndex
          (P.optimized.family.problem.exec.computePubAt
            ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state then 1 else 0 := by
  have hbase := correctedCanonicalFinalTrace_base_eval P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
    P.optimized.computeNodes_injective P.optimized.basis P.optimized.computeChallenge
    P.optimized.computePublic P.optimized.orbit
    (⟨0, P.optimized.family.problem.cfg.compRows_pos⟩ :
      Fin P.optimized.family.problem.cfg.compRows) (⟨(j : ℕ), by omega⟩ : Fin 13)
  have hsel := finalBaseCell_selector P.optimized.sampled
    P.optimized.family.problem.cfg.compRows_pos
    (⟨0, P.optimized.family.problem.cfg.compRows_pos⟩ :
      Fin P.optimized.family.problem.cfg.compRows) j
  change (envOfTrace
    (correctedCanonicalFinalTrace P.optimized.sampled
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes
      P.optimized.basis P.optimized.computeChallenge P.optimized.computePublic
      P.optimized.orbit)
    P.optimized.orbit.ω
    (P.optimized.computeNodes ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩)
    P.optimized.computeChallenge P.optimized.computePublic).trace (j : ℕ) = _
  rw [hbase]
  exact hsel

/-- The initial selector check is satisfied outright: the canonical first row's selector vector is
the committed public first-row selector. -/
theorem canonical_selector20_zero :
    ∀ a ∈ selectorErrors (P.computeScalarEnv (canonicalComputeTrace P)) 20, a = 0 := by
  have hpub := P.optimized.computePublicPins.2.1
  have hcoord : ∀ j : Fin 11,
      (P.computeScalarEnv (canonicalComputeTrace P)).trace (j : ℕ) =
        (P.computeScalarEnv (canonicalComputeTrace P)).pub (20 + (j : ℕ)) := by
    intro j
    rw [canonical_scalarEnv_trace P j]
    exact (hpub j).symm
  intro a ha
  simp only [selectorErrors, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using sub_eq_zero.mpr (hcoord 0)
  · simpa using sub_eq_zero.mpr (hcoord 1)
  · simpa using sub_eq_zero.mpr (hcoord 2)
  · simpa using sub_eq_zero.mpr (hcoord 3)
  · simpa using sub_eq_zero.mpr (hcoord 4)
  · simpa using sub_eq_zero.mpr (hcoord 5)
  · simpa using sub_eq_zero.mpr (hcoord 6)
  · simpa using sub_eq_zero.mpr (hcoord 7)
  · simpa using sub_eq_zero.mpr (hcoord 8)
  · simpa using sub_eq_zero.mpr (hcoord 9)
  · simpa using sub_eq_zero.mpr (hcoord 10)

/-- The head of the terminal selector error list, computed on the two committed state indices.
When the first and last compiled rows carry different states this is nonzero, and then the fixed
scalar challenge `0` cannot be a root of the terminal selector RLC. -/
theorem canonical_selector31_head :
    (P.computeScalarEnv (canonicalComputeTrace P)).trace 0 -
        (P.computeScalarEnv (canonicalComputeTrace P)).pub 31 =
      (if (0 : Fin 11) = OptimizedComputeCodec.stateIndex
          (P.optimized.family.problem.exec.computePubAt
            ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).state then 1 else 0) -
        (if (0 : Fin 11) = OptimizedComputeCodec.stateIndex
          (P.optimized.family.problem.exec.computePubAt
            ⟨P.optimized.family.problem.cfg.compRows - 1,
              Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos Nat.one_pos⟩).state
          then 1 else 0) := by
  have h0 := canonical_scalarEnv_trace P 0
  have hpub := P.optimized.computePublicPins.2.2 0
  simp only [Fin.val_zero, Nat.add_zero] at h0 hpub ⊢
  rw [h0]
  congr 1

end ComputeExclusion

section BadChallengeZero

variable {L : Type} [Field L] [Fintype L] [DecidableEq L]

/-- `0` is a root of the value RLC exactly when the head coefficient vanishes, so a nonzero head
excludes the fixed scalar challenge `0` from the bad set. -/
theorem zero_not_mem_valueBadChallenges (a : L) (as : List L) (ha : a ≠ 0) :
    (0 : L) ∉ valueBadChallenges (a :: as) := by
  intro hmem
  unfold valueBadChallenges at hmem
  split at hmem
  · simp only [Finset.mem_filter] at hmem
    have := hmem.2
    simp [valueRlcPolynomial] at this
    exact ha this
  · simp at hmem

theorem finalComputeChallengeTuple_ext {K : Type}
    {x y : FinalComputeChallengeTuple K}
    (h : x.eqA = y.eqA ∧ x.eqB = y.eqB ∧ x.eqC = y.eqC) : x = y := by
  cases x; cases y; cases h.1; cases h.2.1; cases h.2.2; rfl

theorem memoryChallengeTuple_ext {K : Type}
    {x y : MemoryChallengeTuple K}
    (h : x.interPole = y.interPole ∧ x.lambda = y.lambda) : x = y := by
  cases x; cases y; cases h.1; cases h.2; rfl

end BadChallengeZero

/-! ## The accepted optimized chip-level tuple at the phase-correct package -/

section PhaseCorrect

local instance prime97q : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97q : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

variable (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
    (packageP hmoreM).optimized.basis)
variable (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
variable (hwidthP : FormRWidth F97)
variable (hrootAt : ∀ a g : K97cubic,
  (packageP hmoreM).strategy.RootAxisBoundaryAt
    (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g)))


/-- Honest F97 (`packageM`, `kMem = 2`) is accepted at the **deployed** chip
    (`namedFinalMemoryRAP` at `cfg.kMem`, not the retired `k = 1` default). -/
theorem honest_F97_accepted_at_deployed_chip :
    RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip (canonicalMemoryTrace (packageM hmoreM)) :=
  canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent

/-- Phase-correct F97 twin of `honest_F97_accepted_at_deployed_chip`. -/
theorem honest_F97_packageP_accepted_at_deployed_chip :
    RAP.SatisfiesWithPreprocessing (packageP hmoreM).memoryChip (canonicalMemoryTrace (packageP hmoreM)) :=
  canonicalMemoryTrace_satisfies (packageP hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent

/-- The canonical `199/98` compute trace of the phase-correct package's own compute chip. -/
abbrev computeTraceP := canonicalComputeTrace (packageP hmoreM)

/-- The canonical `196/104` memory trace of the phase-correct package's own memory chip. -/
abbrev memoryTraceP := canonicalMemoryTrace (packageP hmoreM)

/-- The optimized chip-level challenge tuple at the coin `coinN a g`. -/
abbrev tupleP (a g : K97cubic) := canonicalProductionTuple (packageP hmoreM) (coinN a g)

/-- Raw scalar slot `36` of the phase-correct package's compute challenge vector is `0`. -/
theorem packageP_scalar_slot36_zero :
    ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).chal finalScalarChallengeBase = 0 := rfl

theorem packageP_first_state :
    ((packageP hmoreM).optimized.family.problem.exec.computePubAt
      ⟨0, (packageP hmoreM).optimized.family.problem.cfg.compRows_pos⟩).state = .s4 := by
  change (execS.computePubAt ⟨0, _⟩).state = _
  rw [computePubAtS_zero]
  rfl

theorem packageP_last_state :
    ((packageP hmoreM).optimized.family.problem.exec.computePubAt
      ⟨(packageP hmoreM).optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt (packageP hmoreM).optimized.family.problem.cfg.compRows_pos Nat.one_pos⟩).state
      = .s0 := by
  change (execS.computePubAt ⟨1, _⟩).state = _
  rw [computePubAtS_one]
  rfl

theorem packageP_selector31_head :
    ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).trace 0 -
      ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).pub 31 = -1 := by
  rw [canonical_selector31_head (packageP hmoreM), packageP_first_state, packageP_last_state]
  norm_num [OptimizedComputeCodec.stateIndex]


theorem packageP_scalar_slot36_good :
    ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).chal finalScalarChallengeBase ∉
      finalSelectorBadChallenges ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)) := by
  rw [packageP_scalar_slot36_zero]
  have h20 : selectorBadChallenges ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)) 20 = ∅ := by
    unfold selectorBadChallenges
    exact valueBadChallenges_eq_empty_of_all_zero _ (canonical_selector20_zero (packageP hmoreM))
  intro hbad
  rw [finalSelectorBadChallenges, h20, Finset.empty_union] at hbad
  unfold selectorBadChallenges at hbad
  rw [show selectorErrors ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)) 31 =
      (((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).trace 0 -
        ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)).pub 31) ::
      (selectorErrors ((packageP hmoreM).computeScalarEnv (computeTraceP hmoreM)) 31).tail from rfl] at hbad
  refine zero_not_mem_valueBadChallenges _ _ ?_ hbad
  rw [packageP_selector31_head]
  exact neg_ne_zero.mpr one_ne_zero


theorem packageP_compute_outside_failure :
    (canonicalComputeChallengeTuple (packageP hmoreM)) ∉
      extensionFinalComputeCollisionEvent ((packageP hmoreM).computeSourceEnv (computeTraceP hmoreM))
        ((packageP hmoreM).computeWalkEnv (computeTraceP hmoreM)) := by
  simp [extensionFinalComputeCollisionEvent]

/-- **The optimized chip-level acceptance at the phase-correct package**, at every sampled
walk-challenge pair. -/
theorem packageP_optimized_acceptance (a g : K97cubic)
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97)
    (hroot : (packageP hmoreM).strategy.RootAxisBoundaryAt
      (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (packageP hmoreM).OptimizedHistoricalAcceptanceAt (computeTraceP hmoreM) (memoryTraceP hmoreM) (tupleP hmoreM a g) :=
  canonicalProductionAcceptance (packageP hmoreM) (coinN a g)
    (packageP_accepts hmoreM a g hroot) rfl rfl hmoreM
    MultiRootServedFixture.execS_cprimeCoherent haxP hbasisP hwidthP

/-! ### The optimized false-acceptance set at the exhibited traces

Unlike the P8 predicate `Strategy.Accepts`, the optimized chip-level predicate carries the
`same_problem` field, whose whole-problem equality pins the sampled seed and `alphaM` to the
committed configuration's own challenges.  So at the exhibited trace pair
the accepted set is *exactly* the committed fibre, and the false-acceptance set is empty. -/

theorem cfgS_challenges_z : cfgS.challenges.z = servedSeed := by
  have h := congrArg (fun Q : RawProblem F97 K97cubic => Q.cfg.challenges.z)
    specializedProblemM_honest
  simpa [specializedProblem_seed] using h.symm

theorem cfgS_challenges_alpha : cfgS.challenges.α = fixtureAlpha := by
  have h := congrArg (fun Q : RawProblem F97 K97cubic => Q.cfg.challenges.α)
    specializedProblemM_honest
  simpa [specializedProblem_tableAlpha] using h.symm

/-- **Optimized acceptance pins the coin to the committed fibre.**  This is the sub-goal named earlier
for the P8 layer; at the optimized layer it is discharged, because the `same_problem` field is
part of the acceptance record. -/
theorem packageP_sameProblem_pins_fibre (ω : JointCoins K97cubic) (lmb : K97cubic)
    (hsame : (packageP hmoreM).OptimizedSameProblemAt ω lmb) :
    nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha := by
  have hcfg := congrArg RawProblem.cfg hsame.specialized_eq_objects
  constructor
  · have hz : nprSeed ω = (packageP hmoreM).objects.cfg.challenges.z := by
      calc
        nprSeed ω =
            (specializedProblem (packageP hmoreM).optimized.verifier.raw.timestamp
              (nprSeed ω) hsame.nprSeed_ne (alphaM ω) lmb).cfg.challenges.z :=
          (specializedProblem_seed _ _ _ _ _).symm
        _ = (packageP hmoreM).objects.cfg.challenges.z :=
          congrArg (fun cfg : ExactConfig F97 K97cubic => cfg.challenges.z) hcfg
    rw [hz]
    exact cfgS_challenges_z
  · have hα : alphaM ω = (packageP hmoreM).objects.cfg.challenges.α := by
      calc
        alphaM ω =
            (specializedProblem (packageP hmoreM).optimized.verifier.raw.timestamp
              (nprSeed ω) hsame.nprSeed_ne (alphaM ω) lmb).cfg.challenges.α :=
          (specializedProblem_tableAlpha _ _ _ _ _).symm
        _ = (packageP hmoreM).objects.cfg.challenges.α :=
          congrArg (fun cfg : ExactConfig F97 K97cubic => cfg.challenges.α) hcfg
    rw [hα]
    exact cfgS_challenges_alpha

theorem packageP_optimized_acceptance_pins_fibre
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : (packageP hmoreM).OptimizedHistoricalAcceptanceAt (computeTraceP hmoreM) (memoryTraceP hmoreM) c) :
    nprSeed c.1 = servedSeed ∧ alphaM c.1 = fixtureAlpha :=
  packageP_sameProblem_pins_fibre hmoreM c.1 c.2.2.2.lambda hacc.same_problem

/-- **Optimized acceptance pins IO and the internal pole.**  `(a, b, c)` at
`c.2.2.1` are sampled (H1.U exit 1) and have no pin field, so they stay
whatever the candidate supplied. -/
theorem packageP_optimized_acceptance_pins_tuple
    (haxP : FormRAxisBound (packageP hmoreM).optimized.sampled
      (packageP hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageP hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97)
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : (packageP hmoreM).OptimizedHistoricalAcceptanceAt (computeTraceP hmoreM) (memoryTraceP hmoreM) c) :
    c.2 =
      (((packageP hmoreM).optimized.sampled.sampled.coins.gamma,
          (packageP hmoreM).optimized.sampled.sampled.coins.pole),
        (c.2.2.1, ⟨(canonicalMemoryChallengeTuple (packageP hmoreM)).interPole, c.2.2.2.lambda⟩)) := by
  refine Prod.ext hacc.sampled_io_coins (Prod.ext rfl ?_)
  exact memoryChallengeTuple_ext (by
    have h := hacc.memory_intermediate_pole ⟨0, (packageP hmoreM).optimized.family.problem.cfg.memRows_pos⟩
    have hcan := (canonicalTraceAcceptance (packageP hmoreM) hmoreM
        MultiRootServedFixture.execS_cprimeCoherent
      haxP hbasisP hwidthP).memory_intermediate_pole
      ⟨0, (packageP hmoreM).optimized.family.problem.cfg.memRows_pos⟩
    exact ⟨h.symm.trans hcan, rfl⟩)

/-! ### Where the P8 layer and the optimized layer part company

The earlier analysis reduced the classification of the two `p8_fixed_field_*` conjuncts to one sub-goal:
`Accepts ω → nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha`.  At the optimized layer the
*same* sub-goal is discharged above, and the reason is structural rather than mathematical: the
optimized acceptance record carries `OptimizedSameProblemAt` as a **field**, whose whole-problem
equality forces the two sampled coordinates.  `ProductionStrategy.Accepts` has no such field, so
the reduction does not transfer.  The theorem below states exactly that asymmetry on the one
package, without asserting anything about whether the P8 sub-goal is true. -/
theorem fibre_pinning_is_carried_by_same_problem_only
    (hrootAt : ∀ a g : K97cubic,
      (packageP hmoreM).strategy.RootAxisBoundaryAt
        (nprSeed (coinN a g)) seedM_ne (alphaM (coinN a g))) :
    (∀ c : OptimizedProductionChallengeTuple K97cubic F97,
        (packageP hmoreM).OptimizedHistoricalAcceptanceAt (computeTraceP hmoreM) (memoryTraceP hmoreM) c →
        nprSeed c.1 = servedSeed ∧ alphaM c.1 = fixtureAlpha) ∧
      (∀ (ω : JointCoins K97cubic) (lmb : K97cubic),
        (packageP hmoreM).OptimizedSameProblemAt ω lmb →
        nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha) ∧
      (∀ ω : JointCoins K97cubic, nprSeed ω = servedSeed → alphaM ω = fixtureAlpha →
        (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam) :=
  ⟨packageP_optimized_acceptance_pins_fibre hmoreM, packageP_sameProblem_pins_fibre hmoreM,
    fun _ hz hα => packageP_accepts_fibre hmoreM hrootAt hz hα⟩

/-! ### Two of the earlier four remaining P8 failure events, resolved seed-generically

The earlier analysis localized the two `p8_fixed_field_*` conjuncts to four events: collision, specialized
topology, guarded axis, and size window.  Two of the four are settled here without any pinning
hypothesis, by inspecting the committed census and the committed skeleton directly. -/

/-- **The combined comparison census of this fixture separates at every seed.**  All fourteen
census pairs — eleven `skeletonPairs` and three `edgePairs` — are self-comparisons once the
committed nouns are unfolded, and `SepSeed z P P` is vacuously true for every `z`
. -/
theorem censusM_sepSeed_everywhere (z : K97cubic) (i : Fin censusM.census.count) :
    GlobalCarryRecognizer.SepSeed z (censusM.census.pair i).1 (censusM.census.pair i).2 := by
  set P := censusM.census.pair i with hP
  have hmem : P ∈ EdgeComparisonCensus.combinedSkeletonPairs K97cubic skelM := by
    rw [hP]
    exact List.get_mem _ _
  clear_value P
  clear hP
  rw [EdgeComparisonCensus.combinedSkeletonPairs, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rw [BoundSemanticTrace.skeletonPairs, skeletonComparisonCensusM] at hmem
    simp [P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      P8Census.skeletonSubformula, P8Census.skeletonMemoryAxis,
      SemanticTrace.ComparisonUse.pair, skelM, skeletonOfNodes, computeNodesM,
      mapNTree, parentNode, parentSkeletonRow, servedSkeletonRow,
      SemanticSkeleton.publicClaim, decActive, hasTailDecomposition,
      servedRecordSkeleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [GlobalCarryRecognizer.SepSeed, parentFormulaS, parentHeadS, formulaS,
        subjectS, resultS, headS, tailS, parentResultS, ComputeTable.fanoutComp,
        incMod_atom7_eq, Nock.Framework.recordCount]
  · rw [EdgeComparisonCensus.edgePairs] at hmem
    simp [skelM, skeletonOfNodes, computeNodesM, mapNTree, parentNode, servedNode,
      bfsForest, EdgeComparisonCensus.rowEdgePairs,
      EdgeComparisonCensus.edgeTriple, NTree.childOpt,
      P8Census.skeletonSubformula, parentSkeletonRow, servedSkeletonRow,
      ComputeTable.fanoutComp] at hmem
    rcases hmem with rfl | rfl | rfl <;>
      simp [GlobalCarryRecognizer.SepSeed, formulaS, subjectS, headS, tailS]

/-- **The collision failure event of this fixture is empty**, at every coin and not only on the
committed fibre.  One of the earlier four remaining events therefore drops out unconditionally. -/
theorem collisionFailureEventM_empty :
    collisionFailureEvent censusM.census = (∅ : Finset (JointCoins K97cubic)) := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  rw [mem_collisionFailureEvent_iff] at hω
  obtain ⟨i, hi⟩ := hω
  exact hi (censusM_sepSeed_everywhere (nprSeed ω) i)

/-- **The size-window failure event of this fixture is exactly the low-order-seed event.**  The
committed skeleton's only required window noun is the atom `resultS`, whose leaf count is `1`, so
the window reduces to `1 < orderOf z`. -/
theorem sizeWindowFailureM_iff (ω : JointCoins K97cubic) :
    ω ∈ SizeWindowCounting.SizeWindowFailure skelM ↔
      nprSeed ω ≠ 0 ∧ ¬ (1 < orderOf (nprSeed ω)) := by
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff, sizeWindowNounsM]
  constructor
  · rintro ⟨hz, n, hn, hw⟩
    rw [List.mem_singleton] at hn
    subst hn
    refine ⟨hz, fun hord => hw ?_⟩
    exact { one_lt_order := hord
            leaves_lt_order := by simpa [resultS, Noun.leaves] using hord }
  · rintro ⟨hz, hord⟩
    exact ⟨hz, resultS, List.mem_singleton_self _, fun hw => hord hw.one_lt_order⟩

/-- **The P8 false-acceptance emptiness, reduced to three event exclusions.**  This replaces
The earlier route (ii): with the collision event now empty and the zero-seed event excluded by
`accepts_seed_ne_zero`, what remains is exactly the specialized-topology, guarded-axis and
low-order-seed exclusions *at accepted coins*.  This premise set is strictly weaker than the earlier
`Accepts ω → nprSeed ω = servedSeed ∧ alphaM ω = fixtureAlpha`, which implies all three.  None of
the three is discharged here. -/
theorem falseAcceptanceP_empty_of_three_events
    (htopology : ∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
      ω ∉ specializedTopologyFailureEvent verifierP.raw cfgS.challenges.lam)
    (haxis : ∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
      ω ∉ ProductionP8Containment.guardedAxisFailureEvent (packageP hmoreM).strategy
        cfgS.challenges.lam)
    (hwindow : ∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
      1 < orderOf (nprSeed ω)) :
    ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro ω hω
  have hacc := (ProductionP8Containment.mem_falseAcceptanceSet_iff _ _ _ _ _).1 hω
  refine hacc.2 ((packageP hmoreM).containment ω cfgS.challenges.lam hacc.1 ?_)
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact accepts_seed_ne_zero hacc.1 ((mem_zeroSeedFailureEvent_iff ω).1 hbad)
        · rw [mem_collisionFailureEvent_iff] at hbad
          obtain ⟨i, hi⟩ := hbad
          exact hi (censusM_sepSeed_everywhere (nprSeed ω) i)
      · exact htopology ω hacc.1 hbad
    · exact haxis ω hacc.1 hbad
  · exact ((sizeWindowFailureM_iff ω).1 hbad).2 (hwindow ω hacc.1)

/-- The recorded Part-2 state at the phase-correct package: the collision event is empty at every
seed, the size-window event is exactly the low-order-seed event, and emptiness of the P8
false-acceptance set now waits on three named exclusions rather than on the earlier single stronger
fibre-pinning hypothesis.  The two `p8_fixed_field_*` conjuncts remain **unclassified**. -/
theorem p8_fixed_field_status_after_census :
    collisionFailureEvent censusM.census = (∅ : Finset (JointCoins K97cubic)) ∧
      (∀ ω : JointCoins K97cubic,
        ω ∈ SizeWindowCounting.SizeWindowFailure skelM ↔
          nprSeed ω ≠ 0 ∧ ¬ (1 < orderOf (nprSeed ω))) ∧
      ((∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
          ω ∉ specializedTopologyFailureEvent verifierP.raw cfgS.challenges.lam) →
        (∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
          ω ∉ ProductionP8Containment.guardedAxisFailureEvent (packageP hmoreM).strategy
        cfgS.challenges.lam) →
        (∀ ω : JointCoins K97cubic, (packageP hmoreM).strategy.Accepts ω cfgS.challenges.lam →
          1 < orderOf (nprSeed ω)) →
        ProductionP8Containment.FalseAcceptanceSet (packageP hmoreM).strategy 97 3 cfgS.challenges.lam = ∅) :=
  ⟨collisionFailureEventM_empty, sizeWindowFailureM_iff, falseAcceptanceP_empty_of_three_events hmoreM⟩

end PhaseCorrect

end

end Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.specializedProblem_congr
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalComputeTrace
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalMemoryTrace
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalComputeTrace_satisfies
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalMemoryTrace_satisfies
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalComputeChallengeTuple
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalMemoryChallengeTuple
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalProductionTuple
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalTraceAcceptance
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonicalProductionAcceptance
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_memoryBaseEnv
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_memorySourceEnv
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_memory_collision_good
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.honest_F97_accepted_at_deployed_chip
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.honest_F97_packageP_accepted_at_deployed_chip
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.honest_matmul_accepted_at_deployed_chip
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.honest_peano_fib_accepted_at_deployed_chip
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_memory_outside_failure
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_nonterminal_nonIO_source_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_row_collisionFree
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_challenge9_good
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_walkInit_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_challenge11_good
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_scalarEnv_trace
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_selector20_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.canonical_selector31_head
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.zero_not_mem_valueBadChallenges
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.finalComputeChallengeTuple_ext
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.memoryChallengeTuple_ext
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.computeTraceP
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.memoryTraceP
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.tupleP
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_scalar_slot36_zero
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_first_state
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_last_state
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_selector31_head
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_scalar_slot36_good
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_compute_outside_failure
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_optimized_acceptance
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.cfgS_challenges_z
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.cfgS_challenges_alpha
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_sameProblem_pins_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_optimized_acceptance_pins_fibre
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.packageP_optimized_acceptance_pins_tuple
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.fibre_pinning_is_carried_by_same_problem_only
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.censusM_sepSeed_everywhere
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.collisionFailureEventM_empty
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.sizeWindowFailureM_iff
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.falseAcceptanceP_empty_of_three_events
#print axioms Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance.p8_fixed_field_status_after_census
