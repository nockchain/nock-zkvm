/-
  Nock/NockVMROM/Thm54/StrictRawStrategy.lean

  `StrictRawP8Strategy` is the challenge-ordered prover interface implied by parts 1 and 2:

  * `beforeSeed : SkeletonCommitment` is a *field*, so all semantic noun/tree data is fixed once,
    before any seed;
  * `afterSeed z hz` returns raw arrays plus two **deterministic verifier checks** — the phase
    equation `family.cfg.challenges.z = z` and the active-fingerprint scan against the *same*
    `beforeSeed`;
  * `afterCoins` is the coin-phase data-only continuation (topology child payloads and walk arrays).

  ## What "data-only" means here, precisely

  The type carries **no** `BindsAt` field, **no** operational-evidence field, **no** acceptance
  (`RawMessage.Accepts` / `VerifierChecks`) field, **no** table-WF, encoder-injectivity, IO-capacity,
  walk-certificate, semantic-trace, or evaluator field.

  That this is genuinely no extra structure is *compiled*, not asserted:
  `postSeedRawCommitment_ext` and `strictRawP8Strategy_ext` show that two values agreeing on the
  data fields are equal, so the `Prop` fields carry no information; `strictRawP8Strategy_exact_shape`
  is the eta receipt in the style of `ProductionP8Containment.productionRawTimestamp_exact_shape`.

  ## Scope

  No acceptance theorem is claimed.
-/

import Nock.NockVMROM.Thm54.ActiveFingerprintScan
import Nock.NockVMROM.Thm54.RawTopologyAIR

namespace Nock.NockVMROM.Thm54.StrictRawStrategy

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ActiveFingerprintScan

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ}

/-! ## The post-seed message -/

/-- **The post-seed raw commitment.**  Raw data (family + message arrays) together with the two
deterministic post-seed checks.  Its type mentions the pre-seed `C`, which is what forbids choosing
the semantic nouns after seeing `z`. -/
structure PostSeedRawCommitment (F K : Type) [Field F] [Field K] [Algebra F K]
    (p : ℕ) (C : SkeletonCommitment) (z : K) where
  /-- The raw family, whose committed configuration/execution arrays hold the fingerprints. -/
  family : RawPlusIOSegmentedFamily F K
  /-- The raw prover message: table, walk, and IO auxiliary arrays.  All data. -/
  message : RawMessage family p
  /-- Phase pin: the family's committed NPR seed is the sampled one. -/
  sampledSeed : family.cfg.challenges.z = z
  /-- Every active committed fingerprint is `enc z` of the corresponding **pre-committed** noun. -/
  fingerprintChecks : ActiveFingerprintChecks p z C message

namespace PostSeedRawCommitment

variable {C : SkeletonCommitment} {z : K}

/-- Eta receipt: the post-seed object is exactly its four fields. -/
theorem exact_shape (P : PostSeedRawCommitment F K p C z) :
    P =
      { family := P.family
        message := P.message
        sampledSeed := P.sampledSeed
        fingerprintChecks := P.fingerprintChecks } :=
  rfl

/-- **The two `Prop` fields carry no data.**  Agreement on the family and the message arrays already
forces equality, so `sampledSeed`/`fingerprintChecks` are checks, not smuggled structure. -/
theorem ext_of_data (A B : PostSeedRawCommitment F K p C z)
    (hfamily : A.family = B.family) (hmessage : HEq A.message B.message) :
    A = B := by
  cases A
  cases B
  cases hfamily
  cases hmessage
  rfl

/-- The scan really is evaluated against the pre-seed commitment `C`. -/
theorem checks (P : PostSeedRawCommitment F K p C z) :
    ActiveFingerprintChecksOn z C P.family :=
  P.fingerprintChecks

end PostSeedRawCommitment

/-! ## The coin-phase continuation -/

/-- **Data-only coin continuation.**  Topology child payloads (committed against the phase-fixed
family) and walk auxiliary arrays.  No proposition at all. -/
structure RawCoinContinuation {C : SkeletonCommitment} {z : K}
    (P : PostSeedRawCommitment F K p C z) where
  /-- Child payload arrays consumed by the verifier-generated topology RAPs. -/
  topology : RawTopologyArrays P.family
  /-- Walk auxiliary columns. -/
  walks : RawWalkArrays K

namespace RawCoinContinuation

variable {C : SkeletonCommitment} {z : K}

theorem exact_shape {P : PostSeedRawCommitment F K p C z} (A : RawCoinContinuation P) :
    A = { topology := A.topology, walks := A.walks } :=
  rfl

/-- The continuation is pure data: it is determined by its two arrays. -/
theorem ext_of_data {P : PostSeedRawCommitment F K p C z}
    (A B : RawCoinContinuation P)
    (htopology : A.topology = B.topology) (hwalks : A.walks = B.walks) :
    A = B := by
  cases A
  cases B
  cases htopology
  cases hwalks
  rfl

end RawCoinContinuation

/-! ## The strict raw strategy -/

/-- Field order is the protocol order: public claim, pre-seed commitment, post-seed raw data, coin-phase
continuation.  `beforeSeed` is a plain field — not a function of `z` — which is the entire content of
"the commitment is fixed before the seed". -/
structure StrictRawP8Strategy (F K : Type) [Field F] [Field K] [Algebra F K] (p : ℕ) where
  /-- The public claim being proved. -/
  claim : P8PublicClaim
  /-- All semantic data, fixed before any challenge. -/
  beforeSeed : SkeletonCommitment
  /-- The public claim is the committed compute-tree root; a deterministic data equation. -/
  claim_eq : beforeSeed.skeleton.publicClaim = claim
  /-- Post-seed raw data, checked against `beforeSeed`. -/
  afterSeed : ∀ z : K, z ≠ 0 → PostSeedRawCommitment F K p beforeSeed z
  /-- Coin-phase data-only continuation. -/
  afterCoins :
    ∀ (ω : JointCoins K) (hz : nprSeed ω ≠ 0),
      RawCoinContinuation (afterSeed (nprSeed ω) hz)

namespace StrictRawP8Strategy

variable (T : StrictRawP8Strategy F K p)

/-- **Exact-shape / eta receipt**, in the style of
`ProductionP8Containment.productionRawTimestamp_exact_shape`: the strategy is exactly a claim, a
pre-seed commitment, the claim equation, and the two staged data continuations.  There is no
`BindsAt`, operational-evidence, semantic-trace, or acceptance field to project. -/
theorem exact_shape :
    T =
      { claim := T.claim
        beforeSeed := T.beforeSeed
        claim_eq := T.claim_eq
        afterSeed := T.afterSeed
        afterCoins := T.afterCoins } :=
  rfl

/-- **No proof-carrying semantic fields.**  Two strategies agreeing on the four data components are
equal; in particular the `Prop` field `claim_eq` (and, via
`PostSeedRawCommitment.ext_of_data`, the post-seed checks) adds no structure that could hide a
semantic witness. -/
theorem ext_of_data (T U : StrictRawP8Strategy F K p)
    (hclaim : T.claim = U.claim)
    (hcommitment : T.beforeSeed = U.beforeSeed)
    (hafterSeed : HEq T.afterSeed U.afterSeed)
    (hafterCoins : HEq T.afterCoins U.afterCoins) :
    T = U := by
  cases T
  cases U
  cases hclaim
  cases hcommitment
  cases hafterSeed
  cases hafterCoins
  rfl

/-! ### The commitment cannot be chosen after the seed -/

/-- The commitment schedule of a strict strategy: a constant function by construction. -/
def commitmentSchedule : (z : K) → z ≠ 0 → SkeletonCommitment :=
  fun _ _ => T.beforeSeed

/-- **The commitment is seed-independent.**  Type-level, `rfl`-level: there is no `z` in
`T.beforeSeed`, so no seed can influence which nouns were committed. -/
theorem commitmentSchedule_const (z₁ z₂ : K) (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    T.commitmentSchedule z₁ h₁ = T.commitmentSchedule z₂ h₂ :=
  rfl

/-- **Every seed's post-seed check is evaluated against the one same commitment.**  Both conjuncts
mention the literal term `T.beforeSeed`. -/
theorem checks_share_commitment (z₁ z₂ : K) (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    ActiveFingerprintChecksOn z₁ T.beforeSeed (T.afterSeed z₁ h₁).family ∧
      ActiveFingerprintChecksOn z₂ T.beforeSeed (T.afterSeed z₂ h₂).family :=
  ⟨(T.afterSeed z₁ h₁).checks, (T.afterSeed z₂ h₂).checks⟩

/-- The committed noun inventory scanned at any seed is one fixed finite list. -/
theorem commitmentNouns_const (z₁ z₂ : K) (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    commitmentNouns (T.commitmentSchedule z₁ h₁) =
      commitmentNouns (T.commitmentSchedule z₂ h₂) :=
  rfl

/-- The strictly weaker interface a post-seed noun chooser would need: a commitment *function* of the
sampled seed.  `looseSchedule` embeds the strict strategy into it, and
`commitmentSchedule_const` shows the image is constant — which is exactly what
`Nock.RedTeam.Batch24A1` separates from the general loose schedule by a compiled non-constant
witness. -/
abbrev LooseCommitmentSchedule (K : Type) [Field K] : Type :=
  (z : K) → z ≠ 0 → SkeletonCommitment

/-- Forgetting the pre-seed fixing. -/
def looseSchedule : LooseCommitmentSchedule K :=
  T.commitmentSchedule

theorem looseSchedule_const (z₁ z₂ : K) (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0) :
    T.looseSchedule z₁ h₁ = T.looseSchedule z₂ h₂ :=
  rfl


/-- **The strict type plus the seed-independent commitment check already force noun realization.**

At every nonzero seed, every enumerated active compute fingerprint of the strategy's own committed
arrays is the global-carry encoding of a `p`-bounded noun that was fixed before the seed — i.e. it
passes `BoundGates.LeafBoundGate`. -/
theorem scanned_fingerprint_realized
    (hcanon : CanonicalCommitmentCheck p T.beforeSeed) (z : K) (hz : z ≠ 0)
    {fp : ComputeTable.FP K}
    (hfp : fp ∈ activeComputeFingerprints T.beforeSeed (T.afterSeed z hz).family) :
    FPRealized z p fp :=
  activeComputeFingerprints_realized hcanon (T.afterSeed z hz).checks hfp

/-- Memory analogue of `scanned_fingerprint_realized`. -/
theorem scanned_memory_fingerprint_realized
    (hcanon : CanonicalCommitmentCheck p T.beforeSeed) (z : K) (hz : z ≠ 0)
    {fp : ComputeTable.FP K}
    (hfp : fp ∈ activeMemoryFingerprints T.beforeSeed (T.afterSeed z hz).family) :
    FPRealized z p fp :=
  activeMemoryFingerprints_realized hcanon (T.afterSeed z hz).checks hfp

/-- The leaf/decode bound gate is discharged at every nonzero seed. -/
theorem scanned_fingerprint_leafBoundGate
    (hcanon : CanonicalCommitmentCheck p T.beforeSeed) (z : K) (hz : z ≠ 0)
    {fp : ComputeTable.FP K}
    (hfp : fp ∈ activeComputeFingerprints T.beforeSeed (T.afterSeed z hz).family) :
    BoundGates.LeafBoundGate z p fp :=
  T.scanned_fingerprint_realized hcanon z hz hfp

/-- **Pre-seed boundedness for free.**  The seed-independent commitment check discharges the whole
established `SemanticSkeleton.BoundedBy` interface consumed downstream. -/
theorem skeletonBoundedBy (hcanon : CanonicalCommitmentCheck p T.beforeSeed) :
    T.beforeSeed.skeleton.BoundedBy p :=
  hcanon.skeletonBoundedBy

end StrictRawP8Strategy

end

end Nock.NockVMROM.Thm54.StrictRawStrategy

#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.PostSeedRawCommitment.exact_shape
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.PostSeedRawCommitment.ext_of_data
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.RawCoinContinuation.exact_shape
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.RawCoinContinuation.ext_of_data
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.exact_shape
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.ext_of_data
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.commitmentSchedule_const
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.checks_share_commitment
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.commitmentNouns_const
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.looseSchedule_const
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.scanned_fingerprint_realized
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.scanned_memory_fingerprint_realized
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.scanned_fingerprint_leafBoundGate
#print axioms Nock.NockVMROM.Thm54.StrictRawStrategy.StrictRawP8Strategy.skeletonBoundedBy
