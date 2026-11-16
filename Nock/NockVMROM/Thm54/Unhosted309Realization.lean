import Nock.NockVMROM.Thm54.Unhosted309Canonical
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.DeployedChipFamily

/-!
# The width-309 compute realization, the chip at a tuple, and the resources

**.  Parallel definitions beside
`OptimizedStrictPackage.OptimizedComputeRealizationAt`, `DeployedChipFamily.computeChipAt` and
`OptimizedStrictNockVMROMPackage.exact_chip_resources`; nothing existing is edited.**

* `OptimizedComputeRealizationAt309` — the same seven pin fields, and the three chip fields at
  the un-hosted chip: `canonical_satisfies` (`canonical_satisfies309`),
  `arbitrary_trace_source_iff` (`satisfies309_iff_sourceLanguage`) and `conditional_row_decode`
  (`conditional_transition_soundness309`, through the width-309 decode `gather309`);
* `optimizedComputeRealization309` builds it from exactly the hypotheses of the deployed
  `optimizedComputeRealization`;
* `witness10_carries` — the IO-terminal witness is the assignment's own, untouched;
* `computeChipAt309` — the chip at a challenge tuple (`computeChalValOfTuple`, the 11-coin
  production tuple: the compute chip reads no memory-walk coin);
* `exact_chip_resources309` — `(e, w, s, d, k) = (3, 309, 418, 4, 2)` and `108 + 168 + 33 = 309`,
  beside `exact_chip_resources`.
-/

namespace Nock.NockVMROM.Thm54

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Module
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinalTrace
open OptimizedComputeCanonicalSatisfaction
open StrictExtension
open Unhosted309
open scoped Polynomial

noncomputable section

namespace Unhosted309

/-- **The width-309 compute realization surface** (mirror of
`OptimizedStrictPackage.OptimizedComputeRealizationAt`). -/
structure OptimizedComputeRealizationAt309
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (nodes : Fin R.problem.cfg.compRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) : Prop where
  rows_pos : 0 < R.problem.cfg.compRows
  nodes_injective : Function.Injective nodes
  adjacent_orbit :
    ∀ (i : Fin R.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < R.problem.cfg.compRows),
      nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i
  challenge_pins : ExactFinalChallengeCoordinates b A chalVal
  public_pins : ExactFinalPublicCoordinates b R rows_pos pubVal
  requests_pins : ExactFinalRequestsCoordinate b A pubVal
  line_origin : ExactFinalLineOrigin R rows_pos
  canonical_satisfies :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP309 rows_pos nodes b chalVal pubVal orbit)
      (correctedCanonicalFinalTrace309 A rows_pos nodes b chalVal pubVal orbit)
  arbitrary_trace_source_iff :
    ∀ P : Fin (ProductionNamedComputeRAP309 rows_pos nodes b chalVal pubVal orbit).rap.w → F[X],
      RAP.SatisfiesWithPreprocessing
          (ProductionNamedComputeRAP309 rows_pos nodes b chalVal pubVal orbit) P ↔
        SourceLanguage309 rows_pos nodes b chalVal pubVal orbit P
  conditional_row_decode :
    ∀ (P : Fin (ProductionNamedComputeRAP309 rows_pos nodes b chalVal pubVal orbit).rap.w → F[X])
      (_hSat : RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP309 rows_pos nodes b chalVal pubVal orbit) P)
      (x : F) (_hx : x ∈ rowNodeSet nodes),
      let envF := envOfTrace P orbit.ω x chalVal pubVal
      let env := gather309 b envF
      env.base.baseTrace 12 = 0 →
      DecodedTransitionSources309 env

/-- **The width-309 compute realization**, from exactly the hypotheses of the deployed
`OptimizedStrictPackage.optimizedComputeRealization`. -/
def optimizedComputeRealization309
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K] [DecidableEq F] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hA : A.ComputeSampledObligations)
    (hn : 0 < R.problem.cfg.compRows)
    (nodes : Fin R.problem.cfg.compRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
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
    OptimizedComputeRealizationAt309 A hA nodes b chalVal pubVal orbit where
  rows_pos := hn
  nodes_injective := hnodes
  adjacent_orbit := hstep
  challenge_pins := hchal
  public_pins := hpub
  requests_pins := hreq
  line_origin := hln
  canonical_satisfies :=
    canonical_satisfies309 A hA hn nodes hnodes b chalVal pubVal orbit hstep hchal hpub hreq hln
      hord hax hbasis hwidth
  arbitrary_trace_source_iff := satisfies309_iff_sourceLanguage hn nodes b chalVal pubVal orbit
  conditional_row_decode := by
    intro Q hSat x hx
    have hsource := (satisfies309_iff_sourceLanguage hn nodes b chalVal pubVal orbit Q).1 hSat
    dsimp only
    intro hlast
    exact conditional_transition_soundness309 (hsource.2 x hx) hlast

/-- **`witness10` / `witness10_accepts` carry over untouched**: the IO-terminal witness of the
309 realization is the assignment's own (it reads no walk host). -/
theorem witness10_carries
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K} (A : SampledIOSameExecutionAssignment R p) :
    FiniteIO.FiniteIOAccepts (honestRecords10 R)
      A.sampled.coins A.witness10 :=
  A.witness10_accepts

/-- **The un-hosted compute chip at a challenge tuple**, beside
`DeployedChipFamily.computeChipAt` (same `chalVal` map, same publics). -/
def computeChipAt309
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F] [DecidableEq K]
    [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h)
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) : FixedPreprocessingRAP F :=
  ProductionNamedComputeRAP309 hn nodes b (DeployedChipFamily.computeChalValOfTuple b c) pubVal orbit

theorem computeChipAt309_fingerprint
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F] [DecidableEq K]
    [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h)
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    let C := computeChipAt309 hn nodes b pubVal orbit c
    C.rap.e = 3 ∧ C.rap.w = 309 ∧ C.rap.s = 418 ∧ C.rap.d = 4 ∧ C.rap.k = 2 :=
  ⟨rfl, rfl, allGates309_length n b, rfl, rfl⟩

end Unhosted309

namespace OptimizedStrictPackage
namespace OptimizedStrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
  (P : OptimizedStrictNockVMROMPackage F K hOrb)

/-- **Resources of the un-hosted compute chip** (beside `exact_chip_resources`, which it does not
replace): `(e, w, s, d, k) = (3, 309, 418, 4, 2)`, and the width is the three-block split
`108 + 168 + 33` of the repartitioned schedule. -/
theorem exact_chip_resources309 :
    let C := Unhosted309.ProductionNamedComputeRAP309 P.family.problem.cfg.compRows_pos
      P.computeNodes P.basis P.computeChallenge P.computePublic P.orbit
    C.rap.e = 3 ∧ C.rap.w = 309 ∧ C.rap.s = 418 ∧ C.rap.d = 4 ∧ C.rap.k = 2 ∧
      C.rap.w = 108 + 168 + 33 := by
  dsimp only
  have hc := Unhosted309.rap309_fingerprint
    (n := P.family.problem.cfg.compRows) P.basis P.computeChallenge P.computePublic P.orbit
    (rowNodeSet P.computeNodes)
  exact ⟨hc.2.2.2.2, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.1⟩

/-- Only the width moves against the deployed chip: `s`, `d`, `k`, `e` are equal. -/
theorem exact_chip_resources309_vs_deployed :
    let C := ProductionNamedComputeRAP P.family.problem.cfg.compRows_pos P.computeNodes
      P.basis P.computeChallenge P.computePublic P.orbit
    let C' := Unhosted309.ProductionNamedComputeRAP309 P.family.problem.cfg.compRows_pos
      P.computeNodes P.basis P.computeChallenge P.computePublic P.orbit
    C'.rap.w = C.rap.w + 6 ∧ C'.rap.s = C.rap.s ∧ C'.rap.d = C.rap.d ∧ C'.rap.k = C.rap.k ∧
      C'.rap.e = C.rap.e := by
  dsimp only
  have h1 := P.exact_chip_resources
  have h2 := P.exact_chip_resources309
  dsimp only at h1 h2
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rfl

end OptimizedStrictNockVMROMPackage
end OptimizedStrictPackage

end

#print axioms Unhosted309.optimizedComputeRealization309
#print axioms OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.exact_chip_resources309

end Nock.NockVMROM.Thm54
