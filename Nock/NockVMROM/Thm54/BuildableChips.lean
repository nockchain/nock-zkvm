import Nock.AxisBridge
import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.NockVMROM.Thm54.StrictActiveDomains
import Nock.NockVMROM.Thm54.OptimizedComputeCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.RawTopologySoundness
import Nock.NockVMROM.Thm54.MemoryHaltRowsBase

/-!
# Universal same-execution optimized chip builder

This module constructs sampled finite-field IO, exact table/walk assignments, strict active
nodes, optimized fixed-preprocessing chips, canonical polynomial traces, and coordinate layouts
from one `BuildableNockExecution`.

The additional input is pre-compilation backend data only. It contains no sampled assignment,
chip, trace, coordinate pin, memory production assignment, topology/axis conclusion, source
recovery, semantic target, or optimized package.
-/

namespace Nock.NockVMROM.Thm54
namespace BuildableChips

open Nock Nock.Framework Nock.Framework.Reify Nock.Reified
open scoped Polynomial
open Module CoordinateBasis StrictExtension
open OptimizedComputeCanonicalSatisfaction OptimizedComputeCorrectedFinal
open OptimizedComputeCollisionBound
open OptimizedComputeFinalTrace OptimizedComputeSameExecution
open OptimizedMemoryCanonicalSatisfaction OptimizedMemoryCanonicalTrace
open OptimizedMemoryRAP OptimizedMemorySameExecution OptimizedMemorySemanticRealization
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- Canonical record pair committed before sampled IO coins. -/
def executionRecords (E : BuildableNockExecution F K) :
    FiniteIO.PreChallengeRecords K 9 where
  requests := E.exec.derivedRequestIO
  responses := E.exec.derivedResponseIO

/-- In-table `mem_record` pair of the paper.  Requests are the
`verify_child` column at the row's own `C'` (`cprimeOf`, `CprimeCoherent`; no placeholder).
Responses are the
`ver`-selected rows at each row's own `C'` (`derivedResponseIO`). -/
def executionInterRecords (E : BuildableNockExecution F K) :
    FiniteIO.PreChallengeRecords K 9 where
  requests := (RowLayout.consumedRecordList E.exec).map
    (fun r => NockVM.encRecC r (E.exec.cprimeOf r))
  responses := E.exec.derivedResponseIO

/-- The ten-slot IO records (tenth slot the request's `1`-based position). -/
def executionRecords10 (E : BuildableNockExecution F K) : FiniteIO.PreChallengeRecords K 10 :=
  RecordCarrier.extRecords E.exec.derivedRequestIO (executionRecords E)

/-- The ten-slot in-table records. -/
def executionInterRecords10 (E : BuildableNockExecution F K) :
    FiniteIO.PreChallengeRecords K 10 :=
  RecordCarrier.extRecords E.exec.derivedRequestIO (executionInterRecords E)

/-- Minimal pre-compilation inputs in addition to one semantic execution. -/
structure Inputs (E : BuildableNockExecution F K) where
  stateTagChar : NodeEncoding.StateTagChar K
  computeWalkAlpha : K
  memoryWalkAlpha : K
  walkGamma : K
  hOrb : ℕ
  basis : Basis (Fin 3) F K
  orbit : StrictOrbitDomain F 3 hOrb
  activeDomains :
    MonolithicActiveDomains orbit E.cfg.compRows
      (RowLayout.memoryM E.exec) (RowLayout.memoryL E.exec)
  ioCoins : FiniteIO.IOCoins K
  ioPoleHitGood :
    ioCoins.pole ∉ FiniteIO.IOPoleHitEvent (executionRecords E) ioCoins.gamma
  ioGammaGood :
    ioCoins.gamma ∉ FiniteIO.IORLCCollisionEvent (executionRecords E)
  ioLogDerivGood :
    ioCoins.pole ∉ FiniteIO.IOLogDerivEvent (executionRecords E) ioCoins.gamma
  /-- Actual verifier-selected compute compiler tuple: extension fold `9`, walk-init fold `11`,
  and raw scalar selector fold `36`. -/
  computeChallenges : FinalComputeChallengeTuple K
  /-- Raw base-field memory compression challenges at physical slots `0..3`. -/
  memoryScalarChallenge : Fin 4 → F
  /-- Extension-valued memory fold challenge reconstructed at semantic slot `6`. -/
  memoryExtensionFold : K
  /-- Twin of `ioPoleHitGood` on the in-table `mem_record` lists at the sampled
  internal pole, not the IO columns (`:509`). -/
  interPoleHitGood :
    memoryExtensionFold ∉ FiniteIO.IOPoleHitEvent (executionInterRecords E) ioCoins.gamma
  /-- Honest `ver = (st = read_root)` on every memory row.
  Threaded into `sampledAssignment.honestVer`; not a package field. -/
  honestVer : ∀ row ∈ E.exec.memoryRows,
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  /-- The IO coins also miss the ten-slot failure event. -/
  ioGood10 :
    (ioCoins.gamma, ioCoins.pole) ∉ FiniteIO.IOFailureEvent (executionRecords10 E)
  /-- The internal pole also misses the ten-slot in-table hit event. -/
  interPoleHitGood10 :
    memoryExtensionFold ∉ FiniteIO.IOPoleHitEvent (executionInterRecords10 E) ioCoins.gamma

def Inputs.withComputeChallenges {E : BuildableNockExecution F K}
    (I : Inputs E) (c : FinalComputeChallengeTuple K) : Inputs E :=
  { I with computeChallenges := c }

/-- The semantic preimage yields exact derived `LmIO`; `E.requestNodup` upgrades it directly to
`LIO`, without replacing or weakening the retained uniqueness premise. -/
theorem execution_lio (E : BuildableNockExecution F K) :
    IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO := by
  let w : SemanticIOPreimage E.cfg E.exec := Classical.choice E.timestampBounds
  exact IO.cor_uni_req_uni_resp E.cfg.Ksz
    E.exec.derivedRequestIO E.exec.derivedResponseIO
    E.requestNodup w.derivedIO_lmio

/-- Call-site discharge of later-seed zeros: vacuous at `kMem ≤ 1`, else a named hypothesis.
This is an `autoParam` tactic (elaborated at each application), not a term default. -/
syntax "later_seed_zeros" : tactic
macro_rules
  | `(tactic| later_seed_zeros) =>
    `(tactic| first
        | exact Nock.NockVMROM.Thm54.BuildableAxisWitness.hmore_of_kMem_le_one _ (by decide)
        | assumption)

/-- Six-family carrier before its symbolic IO public endpoints are selected. -/
def zeroEndpointFamily (E : BuildableNockExecution F K) (I : Inputs E) :
    PlusIOSegmentedFamily F K :=
  PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
    (ExactCanonicalRAPProblem.ofChained E.chained)
    I.stateTagChar I.computeWalkAlpha I.walkGamma I.memoryWalkAlpha
    0 0 0 E.programIOCapacity E.memoryIOCapacity

/-- Exact selected family and six-family assignment, all indexed by `E.cfg/E.exec`. -/
structure ExactFamilyCompletion (E : BuildableNockExecution F K) (I : Inputs E) where
  requests : IOField K
  responses : IOField K
  outMem : IOField K
  exact : PlusIOSameExecutionAssignment
    ((zeroEndpointFamily E I).withIOEndpoints requests responses outMem) (ringChar K)
  six : exact.Satisfies

namespace ExactFamilyCompletion

def family {E : BuildableNockExecution F K} {I : Inputs E}
    (C : ExactFamilyCompletion E I) : PlusIOSegmentedFamily F K :=
  (zeroEndpointFamily E I).withIOEndpoints C.requests C.responses C.outMem

end ExactFamilyCompletion

theorem exactFamilyCompletion_exists
    (E : BuildableNockExecution F K) (I : Inputs E) :
    Nonempty (ExactFamilyCompletion E I) := by
  let R0 := zeroEndpointFamily E I
  have hlio :
      IO.LIO R0.problem.cfg.Ksz
        R0.problem.exec.derivedRequestIO R0.problem.exec.derivedResponseIO := by
    change IO.LIO E.cfg.Ksz E.exec.derivedRequestIO E.exec.derivedResponseIO
    exact execution_lio E
  obtain ⟨requests, responses, outMem, ⟨io⟩⟩ :=
    ExactDerivedIOAssignment.exists_with_public_endpoints_of_LIO
      R0 E.Ksz_lt_ringChar hlio
  let R := R0.withIOEndpoints requests responses outMem
  obtain ⟨A, hA⟩ :=
    PlusIOSameExecutionAssignment.exists_satisfies_of_chained_IO
      (R := R)
      (by
        change ChainedSemanticExactLanguage E.cfg E.exec
        exact E.chained)
      io
  exact ⟨
    { requests := requests
      responses := responses
      outMem := outMem
      exact := A
      six := hA }⟩

def exactFamilyCompletion
    (E : BuildableNockExecution F K) (I : Inputs E) : ExactFamilyCompletion E I :=
  Classical.choice (exactFamilyCompletion_exists E I)

/-- The post-coin finite IO witness exists at exactly the supplied verifier coins. -/
theorem sampledWitness_exists
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ∃ w : FiniteIO.PostChallengeIOWitness (executionRecords E) I.ioCoins,
      FiniteIO.FiniteIOAccepts (executionRecords E) I.ioCoins w := by
  apply FiniteIO.finiteIO_complete_of_LIO (Ksz := E.cfg.Ksz)
    (executionRecords E) I.ioCoins (execution_lio E)
  intro v hv hzero
  exact I.ioPoleHitGood (by
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, hzero⟩)

def sampledWitness
    (E : BuildableNockExecution F K) (I : Inputs E) :
    FiniteIO.PostChallengeIOWitness (executionRecords E) I.ioCoins :=
  Classical.choose (sampledWitness_exists E I)

theorem sampledWitness_accepts
    (E : BuildableNockExecution F K) (I : Inputs E) :
    FiniteIO.FiniteIOAccepts (executionRecords E) I.ioCoins (sampledWitness E I) :=
  Classical.choose_spec (sampledWitness_exists E I)

/-- Existence of a good internal pole at a fixed `γ`.  Twin of
`exists_ioCoins_of_E` on the shorter in-table list. -/
theorem exists_interPole_of_E (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 1 < Fintype.card K) :
    ∃ pole : K, pole ∉ FiniteIO.IOPoleHitEvent (executionInterRecords E) γ ∧
      pole ∉ FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ ∧ pole ≠ 0 :=
  RecordCarrier.exists_pole_ext _ _ γ hcard

theorem executionInterRecords_length_le_memRows
    (E : BuildableNockExecution F K) :
    (executionInterRecords E).requests.length ≤ E.cfg.memRows ∧
      (executionInterRecords E).responses.length ≤ E.cfg.memRows := by
  constructor
  · have hpart := RowLayout.memoryRows_state_partition E.exec
    simp only [executionInterRecords, List.length_map]
    rw [← RowLayout.verifyChildCount_eq_consumed_length]
    rw [E.exec.memoryRows_length] at hpart
    omega
  · simp only [executionInterRecords]
    have hlen := ExactExecution.derivedResponseIO_length_le E.exec
    rw [E.exec.memoryRows_length] at hlen
    exact hlen

/-- The in-table hit-event mass, nine- and ten-slot together, is at most `4 · memRows`. -/
theorem executionInterRecords_card_lt_of_memRows
    (E : BuildableNockExecution F K)
    (h : 4 * E.cfg.memRows + 1 < Fintype.card K) :
    2 * ((executionInterRecords E).requests.length +
      (executionInterRecords E).responses.length) + 1 < Fintype.card K := by
  have h1 := (executionInterRecords_length_le_memRows E).1
  have h2 := (executionInterRecords_length_le_memRows E).2
  omega

/-- Discharge the length bound from a concrete `memRows` numeral and `|K|`. -/
theorem executionInterRecords_card_lt_of_memRows_eq
    (E : BuildableNockExecution F K) {m q : ℕ}
    (hmem : E.cfg.memRows = m) (hcard : Fintype.card K = q)
    (hlt : 4 * m + 1 < q) :
    2 * ((executionInterRecords E).requests.length +
      (executionInterRecords E).responses.length) + 1 < Fintype.card K :=
  executionInterRecords_card_lt_of_memRows E (by rw [hmem, hcard]; exact hlt)

/-- Chosen internal pole at `γ` outside both in-table hit events. -/
def interPoleOfE (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 1 < Fintype.card K) : K :=
  Classical.choose (exists_interPole_of_E E γ hcard)

theorem interPoleOfE_good (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 1 < Fintype.card K) :
    interPoleOfE E γ hcard ∉ FiniteIO.IOPoleHitEvent (executionInterRecords E) γ :=
  (Classical.choose_spec (exists_interPole_of_E E γ hcard)).1

theorem interPoleOfE_good10 (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 1 < Fintype.card K) :
    interPoleOfE E γ hcard ∉ FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ :=
  (Classical.choose_spec (exists_interPole_of_E E γ hcard)).2.1

theorem interPoleOfE_ne_zero (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 1 < Fintype.card K) :
    interPoleOfE E γ hcard ≠ 0 :=
  (Classical.choose_spec (exists_interPole_of_E E γ hcard)).2.2

/-! `interPoleOfE` avoids the active in-table pole hits and `0` only.  The padding rows
(`decompose` / `halt`) carry the zero record with `C' = 1`, whose record RLC is `γ^8`
(`OptimizedCanonicalHostileLists.rlc_encRecC_memRec_zero`), so at `pole = -γ^8` the honest pair
lies in the all-row pole-hit event (`Batch957.honest_pair_hit_of_pole_neg_gamma8`).
`interPoleOfE'` also excludes `-γ^8`: one more bad value, paid by one unit of slack in the
count (`2 · (|requests| + |responses|) + 2 < |K|`).  That slack is a theorem from the
existing `4 · memRows + 1 < |K|` once `K` has an `F`-basis of size `3`
(`interCard'_of_basis`): `|K| = |F|^3` is never `≡ 2 (mod 4)`.  No new hypothesis. -/

/-- `|K| = |F|^3` is never `4m + 2`: a cube is odd or divisible by `8`. -/
theorem card_ne_four_mul_add_two_of_basis (b : Module.Basis (Fin 3) F K) (m : ℕ) :
    Fintype.card K ≠ 4 * m + 2 := by
  classical
  letI : Fintype F := Fintype.ofInjective (algebraMap F K) (algebraMap F K).injective
  have hc : Fintype.card K = Fintype.card F ^ 3 := by
    rw [Module.card_fintype b, Fintype.card_fin]
  intro h
  rw [hc] at h
  have h4 : (Fintype.card F ^ 3) % 4 = 2 := by rw [h]; omega
  rw [Nat.pow_mod] at h4
  have hlt : Fintype.card F % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases (Fintype.card F % 4) <;> simp_all

/-- **The slack for `-γ^8`**: the in-table hit mass plus two (`0` and `-γ^8`) stays below
`|K|`, from the existing `4 · memRows + 1 < |K|` and a cubic basis. -/
theorem interCard'_of_basis (E : BuildableNockExecution F K) (b : Module.Basis (Fin 3) F K)
    (h : 4 * E.cfg.memRows + 1 < Fintype.card K) :
    2 * ((executionInterRecords E).requests.length +
      (executionInterRecords E).responses.length) + 2 < Fintype.card K := by
  have h1 := (executionInterRecords_length_le_memRows E).1
  have h2 := (executionInterRecords_length_le_memRows E).2
  have hne := card_ne_four_mul_add_two_of_basis b E.cfg.memRows
  omega

/-- **Existence of an internal pole avoiding both in-table hit events, `0` and `-γ^8`.** -/
theorem exists_interPole'_of_E (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 2 < Fintype.card K) :
    ∃ pole : K, pole ∉ FiniteIO.IOPoleHitEvent (executionInterRecords E) γ ∧
      pole ∉ FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ ∧ pole ≠ 0 ∧
      pole + γ ^ 8 ≠ 0 := by
  set bad := FiniteIO.IOPoleHitEvent (executionInterRecords E) γ ∪
    FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ ∪ {0} ∪ {-γ ^ 8}
  have h1 := FiniteIO.IOPoleHitEvent_card_le (executionInterRecords E) γ
  have h2 : (FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ).card ≤
      (executionInterRecords E).requests.length + (executionInterRecords E).responses.length :=
    (FiniteIO.IOPoleHitEvent_card_le (executionInterRecords10 E) γ).trans
      (le_of_eq (by simp [executionInterRecords10, RecordCarrier.extRecords_requests,
        RecordCarrier.extRecords_responses]))
  have hlt : bad.card < Fintype.card K := by
    have hu1 := Finset.card_union_le
      (FiniteIO.IOPoleHitEvent (executionInterRecords E) γ ∪
        FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ ∪ {0}) {-γ ^ 8}
    have hu2 := Finset.card_union_le
      (FiniteIO.IOPoleHitEvent (executionInterRecords E) γ ∪
        FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ) {0}
    have hu3 := Finset.card_union_le
      (FiniteIO.IOPoleHitEvent (executionInterRecords E) γ)
      (FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ)
    have hs0 : ({0} : Finset K).card = 1 := Finset.card_singleton 0
    have hs1 : ({-γ ^ 8} : Finset K).card = 1 := Finset.card_singleton _
    simp only [bad]
    omega
  have hne : bad ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨z, -, hz⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  simp only [bad, Finset.mem_union, Finset.mem_singleton, not_or] at hz
  refine ⟨z, hz.1.1.1, hz.1.1.2, hz.1.2, ?_⟩
  intro h0
  exact hz.2 (eq_neg_of_add_eq_zero_left h0)

/-- **The honest internal pole at `γ`**: outside both in-table hit events, nonzero, and
`≠ -γ^8` (the padding rows' record RLC).  Beside `interPoleOfE`, which stays. -/
def interPoleOfE' (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 2 < Fintype.card K) : K :=
  Classical.choose (exists_interPole'_of_E E γ hcard)

theorem interPoleOfE'_good (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 2 < Fintype.card K) :
    interPoleOfE' E γ hcard ∉ FiniteIO.IOPoleHitEvent (executionInterRecords E) γ :=
  (Classical.choose_spec (exists_interPole'_of_E E γ hcard)).1

theorem interPoleOfE'_good10 (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 2 < Fintype.card K) :
    interPoleOfE' E γ hcard ∉ FiniteIO.IOPoleHitEvent (executionInterRecords10 E) γ :=
  (Classical.choose_spec (exists_interPole'_of_E E γ hcard)).2.1

theorem interPoleOfE'_ne_zero (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 2 < Fintype.card K) :
    interPoleOfE' E γ hcard ≠ 0 :=
  (Classical.choose_spec (exists_interPole'_of_E E γ hcard)).2.2.1

/-- The new exclusion: `pole + γ^8 ≠ 0`, i.e. the pole misses the padding rows' record RLC. -/
theorem interPoleOfE'_add_gamma8_ne_zero (E : BuildableNockExecution F K) (γ : K)
    (hcard :
      2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 2 < Fintype.card K) :
    interPoleOfE' E γ hcard + γ ^ 8 ≠ 0 :=
  (Classical.choose_spec (exists_interPole'_of_E E γ hcard)).2.2.2

/-- Honest IO coins outside both the nine- and the ten-slot failure events. -/
theorem exists_ioCoins10_of_length_bound
    (E : BuildableNockExecution F K) (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    ∃ coins : FiniteIO.IOCoins K,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (executionRecords E) ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent (executionRecords10 E) :=
  RecordCarrier.exists_io_coins_ext _ _ hreq hresp hcard

/-- Finite IO strategy from exactly `E`'s lists and the supplied verifier coins. -/
def finiteIOStrategy
    (E : BuildableNockExecution F K) (I : Inputs E) :
    FiniteIO.FiniteIOStrategy K 9 E.cfg.Ksz (ringChar K) where
  records := executionRecords E
  coins := I.ioCoins
  witness := sampledWitness E I
  accepts := sampledWitness_accepts E I
  uniqueRequest := E.requestNodup
  uniqueResponse := (execution_lio E).2.1
  requestRange := by
    simpa [executionRecords] using
      (show IO.InRange E.cfg.Ksz E.exec.derivedRequestIO.length from
        (by rw [(execution_lio E).2.2.length_eq]; exact (execution_lio E).1))
  responseRange := by
    simpa [executionRecords] using (execution_lio E).1.2
  charBound := E.Ksz_lt_ringChar
  gammaGood := I.ioGammaGood
  poleGood := I.ioLogDerivGood

/-- Sampled IO and exact table/walk witnesses share the selected family and exactly `E.cfg/E.exec`.
-/
def sampledAssignment
    (E : BuildableNockExecution F K) (I : Inputs E) :
    SampledIOSameExecutionAssignment
      (exactFamilyCompletion E I).family (ringChar K) where
  exact := (exactFamilyCompletion E I).exact
  sampled := by
    exact finiteIOStrategy E I
  requests_eq := by
    rfl
  responses_eq := by
    rfl
  poleHitGood := by
    exact I.ioPoleHitGood
  interPole := I.memoryExtensionFold
  interPoleHitGood := by
    exact I.interPoleHitGood
  ioGood10 := by
    exact I.ioGood10
  interPoleHitGood10 := by
    exact I.interPoleHitGood10
  honestVer := by
    change ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
    exact I.honestVer

/-- The family's encoder is the
`LT_comp` projection by construction (`ofProblemWithConcreteNodeEncoders`), and the local topology
relation is a theorem of the retained arity-3 traversal
together with row acceptance (the tree's state is the row's state). -/
theorem walkLabelObligations
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (sampledAssignment E I).WalkLabelObligations := by
  refine ⟨fun t => rfl, ?_⟩
  intro t ht
  have hbind := computeBinding_of_exactTopology E.traversal.1 t ht
  refine ⟨?_, hbind.1, hbind.2⟩
  have hrows : E.exec.ComputeRowsAccepted := E.chained.semantic.1
  have hmem : t.label ∈ E.exec.computeRows := List.mem_map_of_mem ht
  exact ((ExactExecution.computeRowsAccepted_iff _).1 hrows _ hmem).1

theorem computeObligations
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (sampledAssignment E I).ComputeSampledObligations :=
  (sampledAssignment E I).computeSampledObligations_of_six
    ((sampledAssignment E I).exact.satisfies_iff_six_concrete_obligations.1
      (exactFamilyCompletion E I).six)
    (walkLabelObligations E I)

/-- The family's memory
encoder is the `x^mem` projection by construction (`ofProblemWithConcreteNodeEncoders`), and the
local topology relation is a theorem of the retained arity-2 traversal together with row acceptance (the tree's state is the row's state). -/
theorem memoryWalkLabelObligations
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (sampledAssignment E I).MemoryWalkLabelObligations := by
  refine ⟨fun t => rfl, ?_⟩
  intro t ht
  have hbind := memoryBinding_of_exactTopology E.traversal.2 t ht
  refine ⟨?_, hbind.1, hbind.2⟩
  have hrows : E.exec.MemoryRowsAccepted := E.chained.semantic.2.1
  have hmem : t.label ∈ E.exec.memoryRows := List.mem_map_of_mem ht
  exact ((ExactExecution.memoryRowsAccepted_iff _).1 hrows _ hmem).1

/-- Primitive memory-chip obligations, with no axis conclusion. -/
def memoryChipAssignment
    (E : BuildableNockExecution F K) (I : Inputs E) :
    MemoryChipAssignment (sampledAssignment E I) :=
  ⟨(sampledAssignment E I).memorySampledObligations_of_six
    ((sampledAssignment E I).exact.satisfies_iff_six_concrete_obligations.1
      (exactFamilyCompletion E I).six)
    (memoryWalkLabelObligations E I)⟩

/-- Exact strict-prefix compute nodes (`N` active rows, `2^hOrb` physical capacity). -/
def computeNodes (E : BuildableNockExecution F K) (I : Inputs E) :
    Fin E.cfg.compRows → F :=
  fun i => strictOrbitPoint I.orbit i

/-- Exact strict-prefix memory nodes (`M+2L` active rows). -/
def memoryNodes (E : BuildableNockExecution F K) (I : Inputs E) :
    Fin E.cfg.memRows → F :=
  fun i => strictOrbitPoint I.orbit i

theorem computeNodes_injective
    (E : BuildableNockExecution F K) (I : Inputs E) :
    Function.Injective (computeNodes E I) :=
  strictOrbitPoint_injective I.orbit I.activeDomains.computeCapacity

theorem memoryCapacity
    (E : BuildableNockExecution F K) (I : Inputs E) :
    E.cfg.memRows ≤ 2 ^ I.hOrb := by
  rw [E.memoryRows_eq_M_add_two_mul_L]
  exact I.activeDomains.memoryCapacity

theorem memoryNodes_injective
    (E : BuildableNockExecution F K) (I : Inputs E) :
    Function.Injective (memoryNodes E I) :=
  strictOrbitPoint_injective I.orbit (memoryCapacity E I)

theorem computeNodes_adjacent
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ∀ i : Fin E.cfg.compRows, ∀ hi : (i : ℕ) + 1 < E.cfg.compRows,
      computeNodes E I ⟨(i : ℕ) + 1, hi⟩ = I.orbit.ω * computeNodes E I i := by
  intro i hi
  exact (strictOrbitPoint_succ I.orbit i).symm

theorem memoryNodes_adjacent
    (E : BuildableNockExecution F K) (I : Inputs E) :
    MemoryOrbitAligned (R := (exactFamilyCompletion E I).family)
      (memoryNodes E I) I.orbit := by
  intro i hi
  change strictOrbitPoint I.orbit ((i : ℕ) + 1) =
    strictOrbitPoint I.orbit i * I.orbit.ω
  rw [← strictOrbitPoint_succ]
  ring

/-- Generic cubic coordinate serialization; no concrete field value occurs. -/
def coordinateBlock (b : Basis (Fin 3) F K) {n : ℕ}
    (v : Fin n → K) (j : ℕ) : F :=
  if h : j / 3 < n then coord b (v ⟨j / 3, h⟩)
    ⟨j % 3, Nat.mod_lt _ (by omega)⟩ else 0

theorem coordinateBlock_reconstruct (b : Basis (Fin 3) F K) {n : ℕ}
    (v : Fin n → K) (q : Fin n) :
    (∑ k : Fin 3, coordinateBlock b v (3 * (q : ℕ) + (k : ℕ)) • b k) = v q := by
  have hdiv : ∀ k : Fin 3, (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by
    intro k
    omega
  have hmod : ∀ k : Fin 3, (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by
    intro k
    omega
  simpa [coordinateBlock, hdiv, hmod, reconstruct] using reconstruct_coord b (v q)

/-- Complete compute challenge coordinates derived from the same table, walk, and sampled IO:
the cubic block `0..35` of the twelve `𝕂` challenges, and `0` above it. -/
def computeChallenge
    (E : BuildableNockExecution F K) (I : Inputs E) (j : ℕ) : F :=
  if j < 36 then
    coordinateBlock I.basis
      (fun q : Fin 12 =>
        exactFinalChallengeWith (sampledAssignment E I) I.computeChallenges q) j
  else 0

def computePublic
    (E : BuildableNockExecution F K) (I : Inputs E) (j : ℕ) : F :=
  let R := (exactFamilyCompletion E I).family
  if j < 6 then
    coordinateBlock I.basis
      (fun q : Fin 2 => if q = 0 then R.computeWalkAlpha else R.computeWalkSeed) j
  else if h9 : 6 ≤ j ∧ j < 9 then
    coord I.basis (sampledAssignment E I).witness10.terminal ⟨j - 6, by omega⟩
  else if 20 ≤ j ∧ j < 31 then
    if j - 20 = OptimizedComputeCodec.stateIndex
        (R.problem.exec.computePubAt ⟨0, R.problem.cfg.compRows_pos⟩).state then 1 else 0
  else if 31 ≤ j ∧ j < 42 then
    if j - 31 = OptimizedComputeCodec.stateIndex
        (R.problem.exec.computePubAt
          ⟨R.problem.cfg.compRows - 1, Nat.sub_lt R.problem.cfg.compRows_pos (by omega)⟩).state
      then 1 else 0
  else 0

theorem computeRequests_pins
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ExactFinalRequestsCoordinate I.basis (sampledAssignment E I) (computePublic E I) := by
  intro k
  have hk := k.isLt
  rw [computePublic, if_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

theorem computeChallenge_pins
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ExactFinalChallengeCoordinatesWith I.basis (sampledAssignment E I)
      I.computeChallenges (computeChallenge E I) := by
  intro q k
  rw [computeChallenge, if_pos (by omega)]
  simp [coordinateBlock,
    show (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) by omega,
    show (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) by omega]

theorem historical_zero_compute_challenges_compatible
    (E : BuildableNockExecution F K) (I : Inputs E) :
    I.computeChallenges = default →
      (∀ q : Fin 12, ∀ k : Fin 3,
        computeChallenge E I (3 * (q : ℕ) + (k : ℕ)) =
          coord I.basis (exactFinalChallenge (sampledAssignment E I) q) k) ∧
      computeChallenge E I OptimizedComputeSubstitution.finalScalarChallengeBase = 0 := by
  intro hc
  constructor
  · intro q k
    rw [computeChallenge_pins E I q k]
    rw [hc]
    fin_cases q <;> simp [exactFinalChallengeWith, exactFinalChallenge]
  · simp [computeChallenge, OptimizedComputeSubstitution.finalScalarChallengeBase]

/-- Slot `36` is not a cubic index. -/
theorem exactFinalChallengeWith_eq_exactFinalChallenge_of_zero_cubic
    (E : BuildableNockExecution F K) (I : Inputs E)
    (c : FinalComputeChallengeTuple K) (q : Fin 12) :
    exactFinalChallengeWith (sampledAssignment E I) c q =
      exactFinalChallenge (sampledAssignment E I) q := by
  fin_cases q <;> simp [exactFinalChallengeWith, exactFinalChallenge]

/-- The released cubic pin `ExactFinalChallengeCoordinates` is independent of raw scalar slot
`36`.  Two challenge maps that agree on the twelve cubic triples are equivalent for that field. -/
theorem ExactFinalChallengeCoordinates_of_eq_on_cubic
    (E : BuildableNockExecution F K) (I : Inputs E)
    (chalVal chalVal' : ℕ → F)
    (h : ∀ q : Fin 12, ∀ k : Fin 3,
      chalVal (3 * (q : ℕ) + (k : ℕ)) = chalVal' (3 * (q : ℕ) + (k : ℕ))) :
    ExactFinalChallengeCoordinates I.basis (sampledAssignment E I) chalVal ↔
      ExactFinalChallengeCoordinates I.basis (sampledAssignment E I) chalVal' := by
  constructor
  · intro hp q k
    rw [← h q k]
    exact hp q k
  · intro hp q k
    rw [h q k]
    exact hp q k

/-- The selector
fold `36` is free. -/
theorem computeChallenge_historical_pins_of_zero_cubic
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ExactFinalChallengeCoordinates I.basis (sampledAssignment E I) (computeChallenge E I) := by
  intro q k
  rw [computeChallenge_pins E I q k]
  rw [exactFinalChallengeWith_eq_exactFinalChallenge_of_zero_cubic E I
    I.computeChallenges q]

theorem historical_pins_of_with_zero_cubic
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hwith : ExactFinalChallengeCoordinatesWith I.basis (sampledAssignment E I)
      I.computeChallenges (computeChallenge E I)) :
    ExactFinalChallengeCoordinates I.basis (sampledAssignment E I) (computeChallenge E I) := by
  intro q k
  rw [hwith q k]
  rw [exactFinalChallengeWith_eq_exactFinalChallenge_of_zero_cubic E I
    I.computeChallenges q]

theorem compute_challenge_tuple_recovery
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (∑ k : Fin 3, computeChallenge E I (3 * 9 + (k : ℕ)) • I.basis k) =
        E.cfg.challenges.lam ∧
      (∑ k : Fin 3, computeChallenge E I (3 * 11 + (k : ℕ)) • I.basis k) = 0 := by
  constructor
  · have hlt : ∀ k : Fin 3, 3 * 9 + (k : ℕ) < 36 := by intro k; omega
    simp only [computeChallenge, hlt, ↓reduceIte]
    -- the completion family's configuration is `E.cfg` (same-execution family).
    have hcfg : (exactFamilyCompletion E I).family.problem.cfg = E.cfg := rfl
    have h := coordinateBlock_reconstruct I.basis
        (fun q : Fin 12 =>
          exactFinalChallengeWith (sampledAssignment E I) I.computeChallenges q) (9 : Fin 12)
    have hlam : (exactFamilyCompletion E I).family.problem.cfg.challenges.lam =
        E.cfg.challenges.lam :=
      congrArg (fun c : ExactConfig F K => c.challenges.lam) hcfg
    simpa using h.trans
      (show exactFinalChallengeWith (sampledAssignment E I) I.computeChallenges 9 =
          E.cfg.challenges.lam from hlam)
  · have hlt : ∀ k : Fin 3, 3 * 11 + (k : ℕ) < 36 := by intro k; omega
    simp only [computeChallenge, hlt, ↓reduceIte]
    simpa [exactFinalChallengeWith, exactFinalChallenge] using
      coordinateBlock_reconstruct I.basis
        (fun q : Fin 12 =>
          exactFinalChallengeWith (sampledAssignment E I) I.computeChallenges q) (11 : Fin 12)

theorem computeChallenge_slot36
    (E : BuildableNockExecution F K) (I : Inputs E) :
    computeChallenge E I OptimizedComputeSubstitution.finalScalarChallengeBase = 0 := by
  simp [computeChallenge, OptimizedComputeSubstitution.finalScalarChallengeBase]

theorem challenge9_substitution_changes_coordinate
    (K : Type*) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 := by
  let e : FinalComputeChallengeTuple K ≃ (K × K × K) :=
    { toFun := fun c => (c.eqA, c.eqB, c.eqC)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro p; rfl }
  rw [Fintype.card_congr e]
  simp [pow_three]

theorem challenge11_substitution_changes_coordinate
    (K : Type*) [Fintype K] :
    Fintype.card (FinalComputeChallengeTuple K) = Fintype.card K ^ 3 :=
  challenge9_substitution_changes_coordinate K

theorem computePublic_pins
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ExactFinalPublicCoordinates I.basis (exactFamilyCompletion E I).family
      (exactFamilyCompletion E I).family.problem.cfg.compRows_pos (computePublic E I) := by
  let R := (exactFamilyCompletion E I).family
  constructor
  · intro q k
    fin_cases q <;> fin_cases k <;>
      simp [computePublic, coordinateBlock]
  constructor
  · intro j
    rw [computePublic]
    simp only [show ¬ 20 + (j : ℕ) < 6 by omega, ↓reduceIte,
      show ¬ (6 ≤ 20 + (j : ℕ) ∧ 20 + (j : ℕ) < 9) by omega, dite_false,
      show 20 ≤ 20 + (j : ℕ) ∧ 20 + (j : ℕ) < 31 by omega]
    by_cases hs : j = OptimizedComputeCodec.stateIndex
        ((exactFamilyCompletion E I).family.problem.exec.computePubAt
          ⟨0, (exactFamilyCompletion E I).family.problem.cfg.compRows_pos⟩).state
    · simp [hs]
    · have hv : (j : ℕ) ≠
          (OptimizedComputeCodec.stateIndex
            ((exactFamilyCompletion E I).family.problem.exec.computePubAt
              ⟨0, (exactFamilyCompletion E I).family.problem.cfg.compRows_pos⟩).state : ℕ) :=
        fun h => hs (Fin.ext h)
      simp [hs, hv]
  · intro j
    rw [computePublic]
    simp only [show ¬ 31 + (j : ℕ) < 6 by omega, ↓reduceIte,
      show ¬ (6 ≤ 31 + (j : ℕ) ∧ 31 + (j : ℕ) < 9) by omega, dite_false,
      show ¬ (20 ≤ 31 + (j : ℕ) ∧ 31 + (j : ℕ) < 31) by omega,
      show 31 ≤ 31 + (j : ℕ) ∧ 31 + (j : ℕ) < 42 by omega]
    by_cases hs : j = OptimizedComputeCodec.stateIndex
        ((exactFamilyCompletion E I).family.problem.exec.computePubAt
          ⟨(exactFamilyCompletion E I).family.problem.cfg.compRows - 1,
            Nat.sub_lt (exactFamilyCompletion E I).family.problem.cfg.compRows_pos
              (by omega)⟩).state
    · simp [hs]
    · have hv : (j : ℕ) ≠
          (OptimizedComputeCodec.stateIndex
            ((exactFamilyCompletion E I).family.problem.exec.computePubAt
              ⟨(exactFamilyCompletion E I).family.problem.cfg.compRows - 1,
                Nat.sub_lt (exactFamilyCompletion E I).family.problem.cfg.compRows_pos
                  (by omega)⟩).state : ℕ) :=
        fun h => hs (Fin.ext h)
      simp [hs, hv]

/-- The honest Inputs field `memoryExtensionFold` is reused as
that value — no new `Inputs` field, so `TraceGen/Gen.lean` is unedited.  Slots `4`/`5` were
`0` until A-mem-2; slot `6` was the dead fold coin until this retarget. -/
def memoryChallengeTargets
    (E : BuildableNockExecution F K) (I : Inputs E) : Fin 9 → K
  | 0 => (exactMemoryRowEnv (sampledAssignment E I)
      ⟨0, (exactFamilyCompletion E I).family.problem.cfg.memRows_pos⟩).chal 0
  | 1 => (exactMemoryRowEnv (sampledAssignment E I)
      ⟨0, (exactFamilyCompletion E I).family.problem.cfg.memRows_pos⟩).chal 1
  | 2 => (exactMemoryRowEnv (sampledAssignment E I)
      ⟨0, (exactFamilyCompletion E I).family.problem.cfg.memRows_pos⟩).chal 2
  | 3 => (exactFamilyCompletion E I).family.memoryWalkAlpha
  | 4 => (sampledAssignment E I).sampled.coins.gamma
  | 5 => (sampledAssignment E I).sampled.coins.pole
  | 6 => I.memoryExtensionFold
  | 7 => (exactFamilyCompletion E I).family.walkGamma
  | 8 => (exactMemoryRowEnv (sampledAssignment E I)
      ⟨0, (exactFamilyCompletion E I).family.problem.cfg.memRows_pos⟩).chal 8

def memoryPublicTargets
    (E : BuildableNockExecution F K) (I : Inputs E) : Fin 3 → K
  | 0 => (exactFamilyCompletion E I).family.memoryWalkAlpha ^
      (exactFamilyCompletion E I).family.problem.cfg.kMem
  | 1 => (exactFamilyCompletion E I).family.memoryWalkSeed
  | 2 => (sampledAssignment E I).witness10.terminal

/-- Complete memory layout: raw scalar challenges `0..3` are separate from the coordinate-expanded
extension challenge block beginning at physical slot `6`. -/
def memoryChallenge
    (E : BuildableNockExecution F K) (I : Inputs E) (j : ℕ) : F :=
  if h4 : j < 4 then I.memoryScalarChallenge ⟨j, h4⟩
  else if 6 ≤ j then coordinateBlock I.basis (memoryChallengeTargets E I) (j - 6)
  else 0

def memoryPublic
    (E : BuildableNockExecution F K) (I : Inputs E) (j : ℕ) : F :=
  if 6 ≤ j then coordinateBlock I.basis (memoryPublicTargets E I) (j - 6) else 0

theorem memoryChallenge_coordinate
    (E : BuildableNockExecution F K) (I : Inputs E) (q : Fin 9) (k : Fin 3) :
    memoryChallenge E I (6 + 3 * (q : ℕ) + (k : ℕ)) =
      coordinateBlock I.basis (memoryChallengeTargets E I)
        (3 * (q : ℕ) + (k : ℕ)) := by
  rw [memoryChallenge, dif_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem memoryPublic_coordinate
    (E : BuildableNockExecution F K) (I : Inputs E) (q : Fin 3) (k : Fin 3) :
    memoryPublic E I (6 + 3 * (q : ℕ) + (k : ℕ)) =
      coordinateBlock I.basis (memoryPublicTargets E I)
        (3 * (q : ℕ) + (k : ℕ)) := by
  rw [memoryPublic, if_pos (by omega)]
  congr 1
  omega

theorem memoryChallenge_reconstruct
    (E : BuildableNockExecution F K) (I : Inputs E) (q : Fin 9) :
    (∑ k : Fin 3, memoryChallenge E I (6 + 3 * (q : ℕ) + (k : ℕ)) • I.basis k) =
      memoryChallengeTargets E I q := by
  rw [show (∑ k : Fin 3,
      memoryChallenge E I (6 + 3 * (q : ℕ) + (k : ℕ)) • I.basis k) =
      ∑ k : Fin 3,
        coordinateBlock I.basis (memoryChallengeTargets E I)
          (3 * (q : ℕ) + (k : ℕ)) • I.basis k by
    apply Finset.sum_congr rfl
    intro k hk
    rw [memoryChallenge_coordinate E I q k]]
  exact coordinateBlock_reconstruct I.basis (memoryChallengeTargets E I) q

theorem memoryPublic_reconstruct
    (E : BuildableNockExecution F K) (I : Inputs E) (q : Fin 3) :
    (∑ k : Fin 3, memoryPublic E I (6 + 3 * (q : ℕ) + (k : ℕ)) • I.basis k) =
      memoryPublicTargets E I q := by
  rw [show (∑ k : Fin 3,
      memoryPublic E I (6 + 3 * (q : ℕ) + (k : ℕ)) • I.basis k) =
      ∑ k : Fin 3,
        coordinateBlock I.basis (memoryPublicTargets E I)
          (3 * (q : ℕ) + (k : ℕ)) • I.basis k by
    apply Finset.sum_congr rfl
    intro k hk
    rw [memoryPublic_coordinate E I q k]]
  exact coordinateBlock_reconstruct I.basis (memoryPublicTargets E I) q

theorem memoryCoordinatePins
    (E : BuildableNockExecution F K) (I : Inputs E) :
    ExactMemoryCoordinatePins (sampledAssignment E I) I.basis
      (memoryChallenge E I) (memoryPublic E I) := by
  constructor
  · intro q
    fin_cases q
    · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (0 : Fin 9)
    · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (1 : Fin 9)
    · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (2 : Fin 9)
  · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (3 : Fin 9)
  · simpa [memoryPublicTargets] using memoryPublic_reconstruct E I (0 : Fin 3)
  · simpa [memoryPublicTargets] using memoryPublic_reconstruct E I (2 : Fin 3)
  · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (4 : Fin 9)
  · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (5 : Fin 9)
  · simpa [memoryChallengeTargets, sampledAssignment] using
      memoryChallenge_reconstruct E I (6 : Fin 9)
  · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (7 : Fin 9)
  · simpa [memoryChallengeTargets] using memoryChallenge_reconstruct E I (8 : Fin 9)

/-- Data-only family embedded in the staged output. -/
def buildRawFamily
    (E : BuildableNockExecution F K) (I : Inputs E) : BuildableRawFamily E :=
  let R := (exactFamilyCompletion E I).family
  { computeWalkAlpha := R.computeWalkAlpha
    memoryWalkAlpha := R.memoryWalkAlpha
    walkGamma := R.walkGamma
    compNodeWidth := R.compNodeWidth
    compNodeEncode := R.compNodeEncode
    memNodeWidth := R.memNodeWidth
    memNodeEncode := R.memNodeEncode
    requests := R.requests
    responses := R.responses
    outMem := R.outMem }

/-- Milestone-3 data constructor. Child payloads are canonical execution-derived lookup payloads;
no topology-correctness proposition is inserted. -/
def buildTopology
    (E : BuildableNockExecution F K) (I : Inputs E) : BuildableTopology E :=
  let raw := buildRawFamily E I
  let R := raw.toRawPlusIOSegmentedFamily
  { raw := raw
    hOrb := I.hOrb
    basis := I.basis
    orbit := I.orbit
    computeNodes := computeNodes E I
    memoryNodes := memoryNodes E I
    computeChallenge := computeChallenge E I
    computePublic := computePublic E I
    memoryChallenge := memoryChallenge E I
    memoryPublic := memoryPublic E I
    computeChipData :=
      ProductionNamedComputeRAP E.cfg.compRows_pos (computeNodes E I) I.basis
        (computeChallenge E I) (computePublic E I) I.orbit
    memoryChipData :=
      namedFinalMemoryRAP E.cfg.memRows_pos (memoryNodes E I) I.basis
        (memoryChallenge E I) (memoryPublic E I) I.orbit E.cfg.kMem
    computeChildPayload := fun i slot => computeLookupPayload R i slot
    memoryChildPayload := fun i slot => memoryLookupPayload R i slot }

/-- Canonical optimized 199/196-column traces for the constructed chips. -/
def buildTraces
    (E : BuildableNockExecution F K) (I : Inputs E) :
    BuildableTopologyTraces (buildTopology E I) where
  compute :=
    correctedCanonicalFinalTrace (sampledAssignment E I) E.cfg.compRows_pos
      (computeNodes E I) I.basis (computeChallenge E I) (computePublic E I) I.orbit
  memory :=
    canonicalFinalMemoryTrace (sampledAssignment E I) (memoryNodes E I) I.basis
      (memoryChallenge E I) (memoryPublic E I) I.orbit

/-- Later-seed zeros are vacuous when `kMem ≤ 1`. -/
theorem hmore_of_kMem_le_one
    (E : BuildableNockExecution F K) (hk : E.cfg.kMem ≤ 1) :
    ∀ i : Fin E.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < E.cfg.kMem →
        (E.exec.memoryPubAt i).pt.counts = 0 ∧
          (E.exec.memoryPubAt i).pt.indicator = 0 :=
  fun _ hpos hlt => False.elim (by omega)

/-- Both actual optimized chips are satisfied. Memory uses the production assignment
(root-zero bridge on `1..kMem`). -/
theorem buildTraceSatisfaction [DecidableEq F]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hln : (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : ∀ i : Fin E.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < E.cfg.kMem →
        (E.exec.memoryPubAt i).pt.counts = 0 ∧
          (E.exec.memoryPubAt i).pt.indicator = 0 := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hC : E.exec.CprimeCoherent)
    (hax : FormRAxisBound (sampledAssignment E I) I.basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F) E.exec) :
    BuildableTraceSatisfaction (buildTopology E I) (buildTraces E I) := by
  constructor
  · exact correctedCanonicalFinalTrace_satisfies_with
      (sampledAssignment E I) (computeObligations E I) I.computeChallenges
      E.cfg.compRows_pos
      (computeNodes E I) (computeNodes_injective E I) I.basis
      (computeChallenge E I) (computePublic E I) I.orbit
      (computeNodes_adjacent E I) (computeChallenge_pins E I) (computePublic_pins E I)
      (computeRequests_pins E I) hln hord hax hbasis hwidth
  · let P : MemoryProductionAssignment (sampledAssignment E I) E.execA :=
      { obligations := (memoryChipAssignment E I).obligations
        exec_encode := E.exec_encode
        axisStructural := E.memoryTrace.axisStructural
        axisRootPolynomial := by
          intro i
          let t := exactAxisTree E.cfg E.execA i
          have hrnd : (readExps t).Nodup := E.memoryTrace.axisStructural.readExps_nodup i
          have hvnd : (verifyExps t).Nodup := E.memoryTrace.axisStructural.verifyExps_nodup i
          apply countsP_zero_of_exactMemoryAxisValidity E.two_ne_zero t hrnd hvnd
            (E.memoryTrace.support i)
          · intro e he
            exact nested_of_readVerifyNested t (E.memoryTrace.axisStructural.ancestry i) e
              (fun q => readCount_le_one q t hrnd)
              (fun q => verifyCount_le_one q t hvnd)
          · intro e he
            exact E.memoryTrace.axisValidity i e he ((E.memoryTrace.support i e).1 he)
        axisRootIndicator := by
          intro i
          let t := exactAxisTree E.cfg E.execA i
          exact indP_zero_of_balanced t (E.memoryTrace.axisStructural.readExps_nodup i)
            (E.memoryTrace.axisStructural.verifyExps_nodup i) (E.memoryTrace.support i)
        rootPubZero := by
          intro i h0
          have hi0 : i = ⟨0, E.cfg.memRows_pos⟩ := Fin.ext h0
          subst hi0
          exact ⟨E.chained.memory_first_counts, E.chained.memory_first_indicator⟩ }
    exact MemoryPaperFactorization.canonicalFinalMemoryTrace_satisfies
      (sampledAssignment E I) P
      (memoryNodes E I) (memoryNodes_injective E I) I.basis
      (memoryChallenge E I) (memoryPublic E I) I.orbit
      (memoryCoordinatePins E I) (memoryNodes_adjacent E I)
      (memoryDenominatorsSafe_of_sampled (sampledAssignment E I))
      hprl (sampledAssignment E I).honestVer hordM hmore
      E.chained.memory_same_lambda hC
      (fun i => MemoryPaperFactorization.hdenAll_of_interPoleHitGood
        (A := sampledAssignment E I)
        (nodes := memoryNodes E I)
        (hnodes := memoryNodes_injective E I)
        (b := I.basis)
        (chalVal := memoryChallenge E I)
        (pubVal := memoryPublic E I)
        (orbit := I.orbit)
        (memoryCoordinatePins E I) (sampledAssignment E I).honestVer hC i)
      (MemoryHaltLeavesHonest.haltLeavesBase_of_rows _ (by exact hhalt))

/-- Challenge substitution changes the physical chip/trace parameters while preserving canonical
construction and forward satisfaction at both verifier tuples. -/
theorem challenge_substitution_traces_satisfy [DecidableEq F]
    (E : BuildableNockExecution F K) (I : Inputs E)
    (hln : (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : ∀ i : Fin E.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < E.cfg.kMem →
        (E.exec.memoryPubAt i).pt.counts = 0 ∧
          (E.exec.memoryPubAt i).pt.indicator = 0 := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (c d : FinalComputeChallengeTuple K)
    (hC : E.exec.CprimeCoherent)
    (haxc : FormRAxisBound (sampledAssignment E (I.withComputeChallenges c))
      (I.withComputeChallenges c).basis)
    (haxd : FormRAxisBound (sampledAssignment E (I.withComputeChallenges d))
      (I.withComputeChallenges d).basis)
    (hbasis : FormRBasis I.basis)
    (hwidth : FormRWidth F)
    (hhalt : MemoryHaltLeavesHonest.HaltRowsBase (F := F) E.exec) :
    BuildableTraceSatisfaction
        (buildTopology E (I.withComputeChallenges c))
        (buildTraces E (I.withComputeChallenges c)) ∧
      BuildableTraceSatisfaction
        (buildTopology E (I.withComputeChallenges d))
        (buildTraces E (I.withComputeChallenges d)) :=
  ⟨buildTraceSatisfaction E (I.withComputeChallenges c) hln hprl hmore hord hordM hC
      haxc (by change FormRBasis I.basis; exact hbasis) hwidth hhalt,
    buildTraceSatisfaction E (I.withComputeChallenges d) hln hprl hmore hord hordM hC
      haxd (by change FormRBasis I.basis; exact hbasis) hwidth hhalt⟩

/-- Constructor signature refining the staged output type. -/
def buildableTopologyConstructor (I : ∀ E : BuildableNockExecution F K, Inputs E) :
    BuildableTopologyConstructor F K :=
  fun E => buildTopology E (I E)

def buildableTraceConstructor (I : ∀ E : BuildableNockExecution F K, Inputs E) :
    BuildableTopologyTraceConstructor (buildableTopologyConstructor I) :=
  fun E => buildTraces E (I E)

/-- Same-object record receipt: substitution of another execution changes this proposition's type.
-/
theorem sampled_records_same_execution
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (sampledAssignment E I).sampled.records.requests = E.exec.derivedRequestIO ∧
      (sampledAssignment E I).sampled.records.responses = E.exec.derivedResponseIO :=
  ⟨rfl, rfl⟩

/-- Same-object raw-family receipt. -/
theorem topology_problem_same_execution
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).rawFamily.problem = ⟨E.cfg, E.exec⟩ :=
  rfl

theorem raw_row_cards
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).computeDomain.card = E.cfg.compRows ∧
      (buildTopology E I).memoryDomain.card =
        RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec := by
  classical
  constructor
  · change (rowNodeSet (computeNodes E I)).card = E.cfg.compRows
    rw [rowNodeSet, Finset.card_image_of_injective _ (computeNodes_injective E I)]
    simp
  · change (rowNodeSet (memoryNodes E I)).card =
      RowLayout.memoryM E.exec + 2 * RowLayout.memoryL E.exec
    rw [rowNodeSet, Finset.card_image_of_injective _ (memoryNodes_injective E I)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact E.memoryRows_eq_M_add_two_mul_L

/-- The constructed chip and trace cannot be substituted independently: both are definitionally
the canonical objects from this exact sampled assignment, nodes, basis, coordinates, and orbit. -/
theorem canonical_objects_same_execution
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).computeChip =
        ProductionNamedComputeRAP E.cfg.compRows_pos (computeNodes E I) I.basis
          (computeChallenge E I) (computePublic E I) I.orbit ∧
      (buildTopology E I).memoryChip =
        namedFinalMemoryRAP E.cfg.memRows_pos (memoryNodes E I) I.basis
          (memoryChallenge E I) (memoryPublic E I) I.orbit E.cfg.kMem ∧
      (buildTraces E I).compute =
        correctedCanonicalFinalTrace (sampledAssignment E I) E.cfg.compRows_pos
          (computeNodes E I) I.basis (computeChallenge E I) (computePublic E I) I.orbit ∧
      (buildTraces E I).memory =
        canonicalFinalMemoryTrace (sampledAssignment E I) (memoryNodes E I) I.basis
          (memoryChallenge E I) (memoryPublic E I) I.orbit :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Exact optimized resource receipt. -/
theorem chip_resources
    (E : BuildableNockExecution F K) (I : Inputs E) :
    (buildTopology E I).computeChip.rap.w = 303 ∧
      (buildTopology E I).computeChip.rap.s = 418 ∧
      (buildTopology E I).memoryChip.rap.w = 205 ∧
      (buildTopology E I).memoryChip.rap.s = 156 := by
  exact ⟨rfl, correctedFinalComputeAllGates_length E.cfg.compRows I.basis,
    (finalMemoryRAP_fingerprint E.cfg.memRows_pos (memoryNodes E I) I.basis
      (memoryChallenge E I) (memoryPublic E I) I.orbit E.cfg.kMem).1,
    (finalMemoryRAP_fingerprint E.cfg.memRows_pos (memoryNodes E I) I.basis
      (memoryChallenge E I) (memoryPublic E I) I.orbit E.cfg.kMem).2.1⟩

/-! ## F73 regression through the generic constructor -/

namespace Concrete

open ConcreteStrictPackage
open OptimizedComputeSampledTrace.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

def strictOrbit73h3 : StrictOrbitDomain F73 3 3 where
  ω := Classical.choose
    (exists_zmod_generator_of_dvd_sub_one 73 24 (by norm_num))
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  order_ω := by
    simpa using Classical.choose_spec
      (exists_zmod_generator_of_dvd_sub_one 73 24 (by norm_num))
  βcoset_ne_zero := one_ne_zero

theorem inputs73_interCard :
    2 * ((executionInterRecords BuildableConcrete.concreteExecution).requests.length +
      (executionInterRecords BuildableConcrete.concreteExecution).responses.length) + 1 <
        Fintype.card K73cubic :=
  executionInterRecords_card_lt_of_memRows BuildableConcrete.concreteExecution (by
    have hmem : BuildableConcrete.concreteExecution.cfg.memRows = 6 := rfl
    have hcard : Fintype.card K73cubic = 73 ^ 3 := by
      rw [Fintype.card_eq_nat_card]
      exact GaloisField.card 73 3 (by norm_num)
    rw [hmem, hcard]
    norm_num)

theorem concrete_honest_ver :
    ∀ row ∈ BuildableConcrete.concreteExecution.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) := by
  simp [BuildableConcrete.concreteExecution, ConcreteStrictPackage.execution_rows,
    ConcreteStrictPackage.dummyHaltRow, ConcreteStrictPackage.dummyHaltPub,
    ConcreteStrictPackage.readRow, ConcreteStrictPackage.decomposeRow,
    ConcreteStrictPackage.headRow, ConcreteStrictPackage.verifyRow,
    ConcreteStrictPackage.tailRow, ConcreteStrictPackage.readPub,
    ConcreteStrictPackage.decomposePub, ConcreteStrictPackage.headPub,
    ConcreteStrictPackage.verifyPub, ConcreteStrictPackage.tailPub]

/-- F73's five memory rows require the valid `hRap=3` strict prefix; this intentionally replaces
the old hand domain attached to the smaller `hRap=2` concrete receipt. -/
def inputs73 : Inputs BuildableConcrete.concreteExecution where
  stateTagChar := by
    intro m hm n hn hmn
    apply CharP.natCast_injOn_Iio K73cubic (ringChar K73cubic)
    · have hp : 11 < ringChar K73cubic := by
        rw [← ConcreteStrictPackage.q_eq_ringChar]
        norm_num
      exact lt_of_le_of_lt hm hp
    · have hp : 11 < ringChar K73cubic := by
        rw [← ConcreteStrictPackage.q_eq_ringChar]
        norm_num
      exact lt_of_le_of_lt hn hp
    · exact hmn
  computeWalkAlpha := honestLegacyFamily.computeWalkAlpha
  memoryWalkAlpha := honestLegacyFamily.memoryWalkAlpha
  walkGamma := honestLegacyFamily.walkGamma
  hOrb := 3
  basis := basis73
  orbit := strictOrbit73h3
  activeDomains :=
    { computeCapacity := by
        norm_num [BuildableConcrete.concreteExecution, ConcreteStrictPackage.cfg]
      memoryCapacity := by
        rw [← BuildableConcrete.concreteExecution.memoryRows_eq_M_add_two_mul_L]
        norm_num [BuildableConcrete.concreteExecution, ConcreteStrictPackage.cfg] }
  ioCoins := ConcreteStrictPackage.ioCoins
  ioPoleHitGood := by
    change ConcreteStrictPackage.ioCoins.pole ∉
      FiniteIO.IOPoleHitEvent
        { requests := (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedRequestIO
          responses := (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedResponseIO }
        ConcreteStrictPackage.ioCoins.gamma
    intro h
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨v, hv, hz⟩ := h
    exact ConcreteStrictPackage.io_compress_ne_zero v hv hz
  ioGammaGood := by
    exact ConcreteStrictPackage.io_gammaGood
  ioLogDerivGood := by
    exact ConcreteStrictPackage.io_poleGood
  computeChallenges := default
  memoryScalarChallenge := fun j =>
    OptimizedMemoryCanonicalSatisfaction.Concrete.honestMemoryChalVal j
  memoryExtensionFold :=
    interPoleOfE BuildableConcrete.concreteExecution ConcreteStrictPackage.ioCoins.gamma
      inputs73_interCard
  interPoleHitGood :=
    interPoleOfE_good BuildableConcrete.concreteExecution ConcreteStrictPackage.ioCoins.gamma
      inputs73_interCard
  honestVer := concrete_honest_ver
  ioGood10 := by
    change (ConcreteStrictPackage.ioCoins.gamma, ConcreteStrictPackage.ioCoins.pole) ∉
      FiniteIO.IOFailureEvent (RecordCarrier.extRecords
        (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedRequestIO
        { requests := (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedRequestIO
          responses := (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedResponseIO })
    rw [ConcreteStrictPackage.derived_request_singleton,
      ConcreteStrictPackage.derived_response_singleton]
    apply RecordCarrier.notMem_IOFailureEvent_extRecords_single
    · rfl
    · intro h
      simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨v, hv, hz⟩ := h
      refine ConcreteStrictPackage.io_compress_ne_zero v ?_ hz
      change v ∈ (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedRequestIO ++
        (ConcreteStrictPackage.exec honestSeed honestAlpha).derivedResponseIO
      rw [ConcreteStrictPackage.derived_request_singleton,
        ConcreteStrictPackage.derived_response_singleton]
      exact hv
  interPoleHitGood10 :=
    interPoleOfE_good10 BuildableConcrete.concreteExecution ConcreteStrictPackage.ioCoins.gamma
      inputs73_interCard

def topology73 : BuildableTopology BuildableConcrete.concreteExecution :=
  buildTopology BuildableConcrete.concreteExecution inputs73

def traces73 : BuildableTopologyTraces topology73 :=
  buildTraces BuildableConcrete.concreteExecution inputs73

theorem concrete_line_origin :
    (BuildableConcrete.concreteExecution.exec.computePubAt ⟨0, BuildableConcrete.concreteExecution.cfg.compRows_pos⟩).ln_prev = 1 := by
  let i0 : Fin (ConcreteStrictPackage.cfg honestSeed honestAlpha).compRows :=
    ⟨0, by norm_num [ConcreteStrictPackage.cfg]⟩
  have hzero : (ConcreteStrictPackage.exec honestSeed honestAlpha).computePubAt i0 =
      computePub honestSeed honestAlpha := computePubAt_zero
  have hi : (⟨0, BuildableConcrete.concreteExecution.cfg.compRows_pos⟩ :
      Fin (ConcreteStrictPackage.cfg honestSeed honestAlpha).compRows) = i0 := Fin.ext rfl
  have hpub : BuildableConcrete.concreteExecution.exec.computePubAt ⟨0, BuildableConcrete.concreteExecution.cfg.compRows_pos⟩ =
      computePub honestSeed honestAlpha := by
    simpa [BuildableConcrete.concreteExecution, hi] using hzero
  rw [hpub]
  rfl

theorem concrete_prl :
    RowLayout.PairedRecordLayout BuildableConcrete.concreteExecution.exec := by
  simp [RowLayout.PairedRecordLayout, RowLayout.consumedRecordList,
    RowLayout.addedRecordList, BuildableConcrete.concreteExecution,
    ConcreteStrictPackage.execution_rows,
    RowLayout.consumedRecords, ConcreteStrictPackage.dummyHaltRow,
    ConcreteStrictPackage.dummyHaltPub, ConcreteStrictPackage.readRow,
    ConcreteStrictPackage.decomposeRow, ConcreteStrictPackage.headRow,
    ConcreteStrictPackage.verifyRow, ConcreteStrictPackage.tailRow,
    ConcreteStrictPackage.readPub, ConcreteStrictPackage.decomposePub,
    ConcreteStrictPackage.headPub, ConcreteStrictPackage.verifyPub,
    ConcreteStrictPackage.tailPub]

theorem concrete_haltRowsBase :
    MemoryHaltLeavesHonest.HaltRowsBase (F := F73) BuildableConcrete.concreteExecution.exec := by
  intro row hrow hst
  have hrows := (ConcreteStrictPackage.execution_rows ConcreteStrictPackage.honestSeed
    ConcreteStrictPackage.honestAlpha).2
  change row ∈ (ConcreteStrictPackage.exec ConcreteStrictPackage.honestSeed
    ConcreteStrictPackage.honestAlpha).memoryRows at hrow
  rw [hrows] at hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf
      (ConcreteStrictPackage.bind_dummyHaltRow _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf
      (ConcreteStrictPackage.bind_readRow _ _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf
      (ConcreteStrictPackage.bind_decomposeRow _ _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf
      (ConcreteStrictPackage.bind_headRow _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf
      (ConcreteStrictPackage.bind_verifyRow _ _) hst
  · exact MemoryHaltLeavesHonest.bindMemoryRow_halt_leaf
      (ConcreteStrictPackage.bind_tailRow _) hst

theorem traceSatisfaction73
    (hax : FormRAxisBound (sampledAssignment BuildableConcrete.concreteExecution inputs73)
      inputs73.basis)
    (hbasis : FormRBasis inputs73.basis)
    (hwidth : FormRWidth F73)
    (hmore : ∀ i : Fin BuildableConcrete.concreteExecution.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < BuildableConcrete.concreteExecution.cfg.kMem →
        (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.counts = 0 ∧
          (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.indicator = 0) :
    BuildableTraceSatisfaction topology73 traces73 :=
  buildTraceSatisfaction BuildableConcrete.concreteExecution inputs73
    concrete_line_origin concrete_prl hmore
    (fun h => by
      have : BuildableConcrete.concreteExecution.cfg.compRows = 1 := rfl
      omega)
    (fun _ => by
      have hrows : BuildableConcrete.concreteExecution.cfg.memRows = 6 := rfl
      have hα : inputs73.memoryWalkAlpha = honestAlpha := rfl
      have hord : orderOf honestAlpha = 9 := honestAlpha_order
      rw [hrows, hα, hord]
      omega)
    (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
      ConcreteStrictPackage.honestAlpha)
    hax hbasis hwidth concrete_haltRowsBase

theorem regression73
    (hax : FormRAxisBound (sampledAssignment BuildableConcrete.concreteExecution inputs73)
      inputs73.basis)
    (hbasis : FormRBasis inputs73.basis)
    (hwidth : FormRWidth F73)
    (hmore : ∀ i : Fin BuildableConcrete.concreteExecution.cfg.memRows,
      0 < (i : ℕ) → (i : ℕ) < BuildableConcrete.concreteExecution.cfg.kMem →
        (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.counts = 0 ∧
          (BuildableConcrete.concreteExecution.exec.memoryPubAt i).pt.indicator = 0) :
    topology73.rawFamily.problem =
        ⟨BuildableConcrete.concreteExecution.cfg, BuildableConcrete.concreteExecution.exec⟩ ∧
      topology73.computeChip.rap.w = 303 ∧ topology73.computeChip.rap.s = 418 ∧
      topology73.memoryChip.rap.w = 205 ∧ topology73.memoryChip.rap.s = 156 ∧
      (∑ k : Fin 3,
        topology73.computeChallenge (3 * 9 + (k : ℕ)) • inputs73.basis k) =
          MemoryTable.formRDefault ∧
      (∑ k : Fin 3,
        topology73.computeChallenge (3 * 11 + (k : ℕ)) • inputs73.basis k) = 0 ∧
      topology73.computeChallenge
        OptimizedComputeSubstitution.finalScalarChallengeBase = 0 ∧
      BuildableTraceSatisfaction topology73 traces73 := by
  exact ⟨topology_problem_same_execution BuildableConcrete.concreteExecution inputs73,
    (chip_resources BuildableConcrete.concreteExecution inputs73).1,
    (chip_resources BuildableConcrete.concreteExecution inputs73).2.1,
    (chip_resources BuildableConcrete.concreteExecution inputs73).2.2.1,
    (chip_resources BuildableConcrete.concreteExecution inputs73).2.2.2,
    (compute_challenge_tuple_recovery BuildableConcrete.concreteExecution inputs73).1,
    (compute_challenge_tuple_recovery BuildableConcrete.concreteExecution inputs73).2,
    computeChallenge_slot36 BuildableConcrete.concreteExecution inputs73,
    traceSatisfaction73 hax hbasis hwidth hmore⟩

end Concrete

end
end BuildableChips
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.BuildableChips.Inputs
#print axioms Nock.NockVMROM.Thm54.BuildableChips.execution_lio
#print axioms Nock.NockVMROM.Thm54.BuildableChips.sampledAssignment
#print axioms Nock.NockVMROM.Thm54.BuildableChips.computeObligations
#print axioms Nock.NockVMROM.Thm54.BuildableChips.memoryChipAssignment
#print axioms Nock.NockVMROM.Thm54.BuildableChips.buildTopology
#print axioms Nock.NockVMROM.Thm54.BuildableChips.buildTraces
#print axioms Nock.NockVMROM.Thm54.BuildableChips.buildTraceSatisfaction
#print axioms Nock.NockVMROM.Thm54.BuildableChips.sampled_records_same_execution
#print axioms Nock.NockVMROM.Thm54.BuildableChips.topology_problem_same_execution
#print axioms Nock.NockVMROM.Thm54.BuildableChips.raw_row_cards
#print axioms Nock.NockVMROM.Thm54.BuildableChips.canonical_objects_same_execution
#print axioms Nock.NockVMROM.Thm54.BuildableChips.historical_zero_compute_challenges_compatible
#print axioms Nock.NockVMROM.Thm54.BuildableChips.exactFinalChallengeWith_eq_exactFinalChallenge_of_zero_cubic
#print axioms Nock.NockVMROM.Thm54.BuildableChips.ExactFinalChallengeCoordinates_of_eq_on_cubic
#print axioms Nock.NockVMROM.Thm54.BuildableChips.computeChallenge_historical_pins_of_zero_cubic
#print axioms Nock.NockVMROM.Thm54.BuildableChips.historical_pins_of_with_zero_cubic
#print axioms Nock.NockVMROM.Thm54.BuildableChips.compute_challenge_tuple_recovery
#print axioms Nock.NockVMROM.Thm54.BuildableChips.computeChallenge_slot36
#print axioms Nock.NockVMROM.Thm54.BuildableChips.challenge9_substitution_changes_coordinate
#print axioms Nock.NockVMROM.Thm54.BuildableChips.challenge11_substitution_changes_coordinate
#print axioms Nock.NockVMROM.Thm54.BuildableChips.challenge_substitution_traces_satisfy
#print axioms Nock.NockVMROM.Thm54.BuildableChips.Concrete.inputs73
#print axioms Nock.NockVMROM.Thm54.BuildableChips.Concrete.regression73
#print axioms Nock.NockVMROM.Thm54.BuildableChips.interCard'_of_basis
#print axioms Nock.NockVMROM.Thm54.BuildableChips.exists_interPole'_of_E
#print axioms Nock.NockVMROM.Thm54.BuildableChips.interPoleOfE'_add_gamma8_ne_zero
