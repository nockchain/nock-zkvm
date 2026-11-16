/-
  Nock/NockVMROM/Thm54/StrictPackage.lean

  ## What this module claims, and what it does not

  It does **not** claim the paper's unconditional Theorem 5.4.  Several residuals of
  Packets A/B/D/E are genuinely open; each of them is carried here as an *explicit named field* of
  `StrictNockVMROMPackage`, reusing the exact residual object of the packet that owns it:

  * `shapeMatch` / `rowFrame` — Packet A's two named A2 data
    (`RawSemanticAssembly.ExecTreeShapeMatchesAt` / `RowFrameChecksAt`), i.e. the arbitrary-prover
    committed topology (B6) that the A1 active-fingerprint scan does not capture;
  * `sizeWindowBound` — the fixed skeleton's noun-size condition used by the counted OP3/OP4/OP6
    size-window event;
  * `memoryLambdaUniform` — Form R assembly premise that every memory row of a specialized
    execution shares row 0's `λ`.  The chip samples one `λ` (`MemoryTable.Pub.lambda`,
    production `MemoryChallengeTuple`) and does not pin each row's copy.

  Nothing here is `:= True`, nothing is assumed via a false premise, and **no**
  `ProductionP8Containment.ProductionStrategy` inhabitant that would discharge those residuals is
  invented.  The honest reading of `strictNockVMROM_of_package` is therefore: *given the named
  residuals, the S1--S8 conjunction holds over ONE threaded execution.  S6 is the segmented
  `102/44` six-family/shared-IO construction; the separately named `199/196` RAPs belong to the
  S5/S8 production clauses and are not identified with that S6 construction.*

  ## What the threading buys

  `StrictThreadedObjects` (Packet 0) carries exactly one `ExactExecution` and pins the encoded
  request/response IO to that execution.  Everything in the package is tied to it:

  * S1's separation tag is `Tag F K objects.cfg.challenges.α objects.cfg.challenges.β objects.cfg.Ksz`
    — the shared challenges and IO bound, not free parameters;
  * S5/S8's two chips have row domains sized by `objects.exec.computeRows` / `memoryRows`
    (`Hc_card` / `Hm_card`), so `N` and `M + 2L` are the shared execution's row counts;
  * S6 is `CombinedCompletenessAt objects.cfg objects.exec`, conditionally constructing all six
    segmented +IO families and shared IO from its explicit semantic/capacity/characteristic inputs;
  * Packet C's finite-field IO argument runs on `objects.reqRecs`/`objects.respRecs`, which
    `StrictThreadedObjects` already forces to be the derived IO;
  * Packet B's shared table/walk row family and the arbitrary-prover verifier's honest
    specialization both reduce to `⟨objects.cfg, objects.exec⟩` (`walkFamily_problem`,
    `honest_specialization`).

  The separate top-level language projection remains forward-only
  (`perfect_completeness_is_forward`), and the bare converse remains refuted next door
  (`LanguageBridge.not_reverse_language_projection`).  It is not substituted for the exact
  combined S6 parameter.

  Of the thirteen `StrictThm54Statement` clauses, **eight** are genuinely threaded to the shared
  `objects.exec` and Nock-bearing (`named_raps`, `shared_io`, `perfect_completeness`, `containment`,
  `walk_bounds`, `fingerprint`, `chip_shape`, `row_budgets`); **five are not**, and a reader must not
  count them as Nock content:
  * `structural` carries the existing S1--S4 surface plus segmented exact S6; this does not identify
    S6's `102/44` construction with the package's named `199/196` chips (G10/R6 remain open);
  * the former arbitrary-field `goldilocks_margin` and separate varying-family `asymptotic` clauses
    have been removed.  Their replacement is the package's own false-acceptance event over its own
    `K`, bounded by the canonical five-class workload divided by `|K|`; the bit-form consequence uses
    that same event and workload.  The general varying-family theorem remains available standalone in
    `StrictAsymptoticSecurity`.

  And no inhabitant of `StrictNockVMROMPackage` exists in
  the tree — `package_nonempty_only_under_residuals` takes `Nonempty` as a *hypothesis*, so the
  conditional is a non-trivial implication whose antecedent's satisfiability is itself open.

  ## Two further disclosures

  * The structural field is the *existing* Tier-2 bundle of `Capstone.lean`, with S1--S4 and exact
    segmented S6 imported as-is.
  * `compLanguage` / `memLanguage` are package fields.
-/

import Nock.NockVMROM.Thm54.StrictReleaseContract
import Nock.NockVMROM.Thm54.LanguageBridgeReverse
import Nock.NockVMROM.Thm54.ServedLookupBridge
import Nock.NockVMROM.Thm54.SharedTableWalkRow
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.StrictAsymptoticSecurity
import Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity
import Nock.NockVMROM.Thm54.ExactOneHot
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.JointVerification
import Nock.NockVMROM.Thm54.StrictG10Cost
import Nock.RedTeam.Batch29Thm54MonolithicRAP
import Nock.NockVMROM.Capstone

namespace Nock.NockVMROM.Thm54
namespace StrictPackage

open scoped Classical
open Module
open Nock Nock.Walk Nock.Reified Nock.Framework Nock.NockVMROM
open Nock.NockVMROM.Thm54.SharedTableWalkRow
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.RawSemanticAssembly
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.StrictAsymptoticSecurity
open Nock.NockVMROM.Thm54.GoldilocksConcreteSecurity
open Nock.NockVMROM.Thm54.ProductionAsymptotic
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ExactPrimeFamily

open scoped Polynomial

noncomputable section

/-! ## 1. The package -/

/-- **The single threaded Theorem-5.4 package.**

Every clause of the capstone below reads its objects out of this one structure.  The fields split
into three kinds, and the docstrings say which is which:

* **shared objects** — one `StrictThreadedObjects`, one verifier, one skeleton commitment, one
  constructed RAP pair over one basis/orbit/row-domain;
* **prover-supplied deterministic data** — the honest chained execution, the A1 active-fingerprint
  scan, the shared table/walk row family with its acceptance data, the finite-field IO strategy, and
  the standing finite-field/census scope of the production containment theorem;
* **Open obligations** — `shapeMatch`, `rowFrame`, `slotSemantics`, `compSemanticTemplate`,
  `memSemanticTemplate`, `recordCountBalance`, `sizeWindowBound`, `memoryLambdaUniform`.  These are exactly the objects left open; they are reused verbatim, never restated and never weakened. -/
structure StrictNockVMROMPackage (F K : Type) [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    (hOrb q Λ : ℕ) where
  /-- **Shared object.** -/
  objects : StrictThreadedObjects F K
  /-- **Shared object.**  The arbitrary prover's template-fixed raw verifier. -/
  verifier : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)
  /-- **Shared object.**  The pre-seed semantic skeleton commitment. -/
  commitment : SkeletonCommitment
  /-- The committed skeleton makes the verifier's own public claim. -/
  claim_eq : commitment.skeleton.publicClaim = verifier.raw.claim
  /-- The honest NPR seed. -/
  honestSeed : K
  /-- `Def:NPR` requires a nonzero seed. -/
  honestSeed_ne : honestSeed ≠ 0
  /-- The honest sampled memory-walk challenge. -/
  honestAlpha : K
  /-- **Single-execution threading.**  The verifier's specialization at the honest coins IS the
  shared execution: the soundness clause and the completeness/cost clauses talk about one machine.
  The Form R `λ` is the shared execution's own sampled `λ` (`objects.cfg.challenges.lam`, drawn
  with `α`); the package carries no separate `λ`. -/
  honest_specialization :
    specializedProblem verifier.raw.timestamp honestSeed honestSeed_ne honestAlpha
        objects.cfg.challenges.lam
      = ⟨objects.cfg, objects.exec⟩
  /-- **Shared object.**  The `e = 3` coordinate basis of the cubic extension. -/
  basis : Basis (Fin 3) F K
  /-- **Shared object.**  The one `Def:RAP` orbit domain, `ord(ω) = e·2^h`. -/
  orbit : StrictOrbitDomain F 3 hOrb
  /-- Challenge-column valuation of the reifier. -/
  chalVal : ℕ → F
  /-- Public-column valuation of the reifier. -/
  pubVal : ℕ → F
  /-- The compute chip's row domain. -/
  Hc : Finset F
  /-- The memory chip's row domain. -/
  Hm : Finset F
  /-- The compute row domain has the shared execution's compute-row count. -/
  Hc_card : Hc.card = objects.exec.computeRows.length
  /-- The memory row domain has the shared execution's memory-row count. -/
  Hm_card : Hm.card = objects.exec.memoryRows.length
  /-- **Shared object.**  The named compute chip. -/
  compRAP : RAP F
  /-- **Shared object.**  The named memory chip. -/
  memRAP : RAP F
  /-- The compute chip is the constructed `RAP_NockComp-IO`. -/
  comp_is_named : compRAP = RAP_NockCompIO basis chalVal pubVal orbit Hc
  /-- The memory chip is the constructed `RAP_NockMem-IO`. -/
  mem_is_named : memRAP = RAP_NockMemIO basis chalVal pubVal orbit Hm
  /-- **Prover data.**  The honest execution is in the chained semantic exact language; this is the
  input of S6's forward completeness bridge. -/
  chained : ChainedSemanticExactLanguage objects.cfg objects.exec
  /-- The deterministic post-seed active-fingerprint scan. -/
  scan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    ActiveFingerprintChecksAt z commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  /-- The purely structural tree-shape datum of the
  arbitrary-prover committed topology; `RawSemanticAssembly` records that no field of the strict raw
  strategy supplies it. -/
  shapeMatch : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    ExecTreeShapeMatchesAt commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  /-- The per-row non-fingerprint frame residual, on exactly the zip
  the A1 scan uses. -/
  rowFrame : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    RowFrameChecksAt z commitment
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec
  /-- The ONE table/walk row family. -/
  walkFamily : RawPlusIOSegmentedFamily F K
  /-- **Single-execution threading.**  The walk family carries the shared execution. -/
  walkFamily_problem : walkFamily.problem = ⟨objects.cfg, objects.exec⟩
  /-- The compute node encoding determines the paper's `LT_comp` label. -/
  compEnc_inj : ∀ a b, walkFamily.compNodeEncode a = walkFamily.compNodeEncode b →
    ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b
  /-- The memory node encoding determines the paper's `x^mem` label. -/
  memEnc_inj : ∀ a b, walkFamily.memNodeEncode a = walkFamily.memNodeEncode b →
    MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b
  /-- **Prover data.**  Canonical compute-row acceptance. -/
  computeRowsAccepted : walkFamily.exec.ComputeRowsAccepted
  /-- **Prover data.**  Canonical memory-row acceptance. -/
  memoryRowsAccepted : walkFamily.exec.MemoryRowsAccepted
  /-- **Prover data.** -/
  topologyBinding : RawTopologyBindingResidual walkFamily
  /-- The two Nock slot facts of every committed compute row, i.e.
  the honest memory reconstruction, stated with no recognizer language. -/
  slotSemantics : ∀ s ∈ computeSkeletonRows commitment.skeleton,
    SkeletonSlotSemantics s
  /-- The two record noun equations of the committed rows. -/
  recordEquations : ∀ s ∈ computeSkeletonRows commitment.skeleton,
    SkeletonRecordEquations s
  /-- **Prover data (Packet C).**  The finite-field IO argument, with its counted-event
  exclusions. -/
  ioStrategy : FiniteIO.FiniteIOStrategy K 9 objects.cfg.Ksz (ringChar K)
  /-- **IO threading.**  The IO argument runs on the shared execution's request records. -/
  io_requests : ioStrategy.records.requests = objects.reqRecs
  /-- **IO threading.**... and on its response records. -/
  io_responses : ioStrategy.records.responses = objects.respRecs
  /-- The `𝕂`-level language the compute template is claimed to present. -/
  compLanguage : Nock.Reified.Env K → Prop
  /-- The `𝕂`-level language the memory template is claimed to present. -/
  memLanguage : Nock.Reified.Env K → Prop
  /-- `B29SemanticTemplate` *defines* the language from the template's own `𝕂`-gates, and `compLanguage`
  is itself a package field, so this field is discharged tautologically (`b29_residual_satisfiable`
  is `Iff.rfl`) and imposes zero constraint on `Nonempty StrictNockVMROMPackage`.  It carries no Nock
  content; the genuine (open) obligation — that the constructed chip's gates ARE the Nock chained
  language at the paper's `(13,62)` census — is NOT captured by this field and lives outside the
  package. -/
  compSemanticTemplate :
    Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (compTemplate F) compLanguage
  /-- As `compSemanticTemplate`: discharged tautologically, zero Nock content, does not capture the open
  Nock-identification obligation. -/
  memSemanticTemplate :
    Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (memTemplate F) memLanguage
  /-- The exact `read_root`/`verify_child` row-count balance
  equivalent to the memory budget `M + 2L`.  This field deliberately does not
  require the stronger optional `PairedRecordLayout` multiset permutation. -/
  recordCountBalance : RowLayout.RecordCountBalanced objects.exec
  /-- **Scope.**  The combined comparison census of the committed skeleton. -/
  census : EdgeComparisonCensus.CombinedSkeletonCensus K commitment.skeleton Λ
  /-- **Local fixed-field size condition.**  Exactly the nouns consumed by
  the OP3/OP4/OP6 size-window checks have at most `Λ` leaves.  Unlike the removed
  `StrategyFamilyData`, this is about this package's one committed skeleton. -/
  sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy commitment.skeleton Λ
  /-- **Scope.**  State-tag separation in `K`. -/
  stateTagChar : NodeEncoding.StateTagChar K
  /-- **Scope.**  The canonical atom range is nontrivial. -/
  q_gt_one : 1 < q
  /-- **Scope.**  The semantic modulus is the characteristic of the execution field. -/
  q_eq_ringChar : q = ringChar K
  /-- **Scope.**  Every committed skeleton atom is below the atom range. -/
  skeletonBounded : commitment.skeleton.BoundedBy q
  /-- **Scope.**  Every combined-census occurrence is likewise bounded. -/
  combinedBounded : CombinedBoundedBy K q commitment.skeleton
  /-- **Scope (Packet C).**  The IO/K-size budget is below the characteristic. -/
  KszBound : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K
  /-- **Scope (Packet C).**  Program-IO capacity at the orbit exponent. -/
  progCapacity : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
      2 ^ (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h
  /-- **Scope (Packet C).**  Memory-IO capacity at the orbit exponent. -/
  memCapacity : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
    (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
      2 ^ (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h

/-! ## 2. The pieces, wired at the shared objects -/

namespace StrictNockVMROMPackage

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb q Λ : ℕ}
  (P : StrictNockVMROMPackage F K hOrb q Λ)

/-- The arbitrary-prover production strategy whose semantic support is *derived* from the
deterministic pre-seed commitment plus the post-seed scan (Packet A step 5), never assumed. -/
def strategy : ProductionStrategy F K :=
  productionStrategy_of_scan P.verifier P.commitment P.claim_eq P.shapeMatch P.rowFrame P.scan

@[simp] theorem strategy_skeleton : P.strategy.skeleton = P.commitment.skeleton := rfl

@[simp] theorem strategy_verifier : P.strategy.verifier = P.verifier := rfl

/-- The characteristic pin derives the bounded-cast injectivity consumed by containment; it is not
independent package data. -/
theorem castInj (package : StrictNockVMROMPackage F K hOrb q Λ) :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q) := by
  rw [package.q_eq_ringChar]
  exact StrictRawReconstruction.charCast_injOn (ringChar K)

/-- The shared IO bound is positive: the semantic preimage of the chained execution forces
`1 ≤ |requests| ≤ Ksz` (`LanguageBridge.one_le_Ksz`). -/
theorem one_le_Ksz : 0 < P.objects.cfg.Ksz := by
  obtain ⟨w⟩ := P.chained.semantic.2.2
  exact Thm54.one_le_Ksz w

/-! ### Top-level language projection, forward only -/

/-- The shared chained execution projects into `L_NockVMROM` at the shared tag.  This is the
*forward* language direction; the bare converse stays refuted
(`LanguageBridge.not_reverse_language_projection`).  The structural bundle's S6 claim is instead
the exact six-family/shared-IO `CombinedCompletenessAt` proposition. -/
theorem perfect_completeness :
    Language
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (stmtOfExact P.objects.cfg P.objects.exec) :=
  perfect_completeness_is_forward P.chained

/-! ### Packet C: the finite-field IO language, on the derived IO -/

/-- **Packet C, threaded.**  The finite-field IO argument concludes the record-level IO language on
the shared execution's own derived request/response records. -/
theorem io_language :
    IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs := by
  have h := P.ioStrategy.lio
  rw [P.io_requests, P.io_responses] at h
  exact h

/-! ### Packet A: the canonical binding, derived from the scan -/

/-- **Packet A step 3, wired.**  The binding is a theorem of the package's scan plus the two named
A2 residuals; the seed pin comes free from the timestamp carrier. -/
theorem binds (z : K) (hz : z ≠ 0) (α lmb : K) :
    BindsAt z P.commitment.skeleton
      (specializedProblem P.verifier.raw.timestamp z hz α lmb).cfg
      (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec :=
  bindsAt_of_scan (specializedProblem_seed P.verifier.raw.timestamp z hz α lmb)
    (P.shapeMatch z hz α lmb) (P.rowFrame z hz α lmb) (P.scan z hz α lmb)


/-- The counted compute-walk failure mass of the shared row family. -/
def computeWalkBadRatio : ℚ :=
  ((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) P.walkFamily.compNodeEncode
      (computeRowLabel P.walkFamily) (computeChildLabel P.walkFamily)
      (foCol P.walkFamily.computeWalkRows) P.walkFamily.cfg.compRows).card : ℚ)
    / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

/-- The compute-walk soundness bound of the shared row family. -/
def computeWalkBound : ℚ :=
  (P.walkFamily.cfg.compRows : ℚ) / (Fintype.card K : ℚ)
    + ((P.walkFamily.cfg.compRows * (P.walkFamily.compNodeWidth - 1) : ℕ) : ℚ)
        / (Fintype.card K : ℚ)

/-- The counted memory-walk failure mass of the shared row family. -/
def memoryWalkBadRatio : ℚ :=
  ((NockVM.walkBadForest (MemoryTable.mem_stateSep (K := K)) P.walkFamily.memNodeEncode
      (memoryRowLabel P.walkFamily) (memoryChildLabel P.walkFamily)
      (foCol P.walkFamily.memoryWalkRows) P.walkFamily.exec.memoryForest.length
      P.walkFamily.cfg.memRows).card : ℚ)
    / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))

/-- The memory-walk soundness bound of the shared row family. -/
def memoryWalkBound : ℚ :=
  (P.walkFamily.cfg.memRows : ℚ) / (Fintype.card K : ℚ)
    + ((P.walkFamily.cfg.memRows * (P.walkFamily.memNodeWidth - 1) : ℕ) : ℚ)
        / (Fintype.card K : ℚ)

/-- `hSf`, `hvalid`, `harity`, `hfo` and `hFcommit` are all
discharged from the package's acceptance data and topology binding residual. -/
theorem computeWalk_bound : P.computeWalkBadRatio ≤ P.computeWalkBound :=
  computeWalk_final_prob_of_acceptance_of_label P.walkFamily.compNodeEncode P.compEnc_inj
    P.walkFamily P.computeRowsAccepted P.topologyBinding

theorem memoryWalk_bound : P.memoryWalkBadRatio ≤ P.memoryWalkBound :=
  memoryWalk_final_prob_of_acceptance_of_label P.walkFamily.memNodeEncode P.memEnc_inj
    P.walkFamily P.memoryRowsAccepted P.topologyBinding

/-! ### S5: package-indexed exact two-RAP realization -/

/-- **Strict S5 on exactly one package**.

This proposition names the package's two monolithic chips, ties both of their row domains to the
same execution, pins the package walk family to that execution, and carries shared derived IO plus
both package walk bounds.  It does not identify these `199/196`, `e = 3` chips with S6's segmented
`102/44`, `e = 1` family. -/
structure StrictTwoRAPRealization : Prop where
  named_raps :
    P.compRAP = RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc ∧
      P.memRAP = RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm
  compute_chip_domain : P.compRAP.H = P.Hc
  memory_chip_domain : P.memRAP.H = P.Hm
  compute_row_domain : P.Hc.card = P.objects.exec.computeRows.length
  memory_row_domain : P.Hm.card = P.objects.exec.memoryRows.length
  walk_family : P.walkFamily.problem = ⟨P.objects.cfg, P.objects.exec⟩
  shared_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  compute_walk_bound : P.computeWalkBadRatio ≤ P.computeWalkBound
  memory_walk_bound : P.memoryWalkBadRatio ≤ P.memoryWalkBound

theorem strictTwoRAPRealization : P.StrictTwoRAPRealization where
  named_raps := ⟨P.comp_is_named, P.mem_is_named⟩
  compute_chip_domain := by
    rw [P.comp_is_named]
    exact expandChip_H (compTemplate F) P.basis P.chalVal P.pubVal P.orbit P.Hc
  memory_chip_domain := by
    rw [P.mem_is_named]
    exact expandChip_H (memTemplate F) P.basis P.chalVal P.pubVal P.orbit P.Hm
  compute_row_domain := P.Hc_card
  memory_row_domain := P.Hm_card
  walk_family := P.walkFamily_problem
  shared_io := P.io_language
  compute_walk_bound := P.computeWalk_bound
  memory_walk_bound := P.memoryWalk_bound

/-! ### Packet A + B2: arbitrary-prover false-acceptance containment -/

/-- **S7 (arbitrary prover), the paper.**  An accepting coin outside the five-class failure
union hits the genuine target, with the semantic binding derived from the scan and the served
lookups traded for the Nock slot facts.  Uniform memory `λ` is a theorem of the template
chronology (`familyAt_memoryLambda`): every specialized row carries the sampled `λ`. -/
theorem containment (ω : JointCoins K) (lmb : K)
    (hacc : P.strategy.Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion P.strategy P.census lmb) :
    ProductionP8Containment.GenuineTargetAt P.strategy q Λ ω lmb :=
  verifierGeneratedTopologyRawContainment_of_slotSemantics P.verifier P.commitment q
    P.claim_eq P.shapeMatch P.rowFrame P.scan P.census P.stateTagChar P.q_gt_one
    P.q_eq_ringChar (StrictNockVMROMPackage.castInj P) P.skeletonBounded P.combinedBounded
    P.recordEquations P.slotSemantics P.KszBound P.progCapacity P.memCapacity ω lmb hacc hout
    (fun hz i => P.verifier.familyAt_memoryLambda ω lmb hz i)

/-! ### S7: same-field pointwise soundness

The paper's capstone states its soundness condition at the same `𝕂` that carries the execution.  A cryptographic `Negligible` predicate still requires a varying family; the
fixed-field content is the exact pointwise `workload / |𝕂|` inequality.  The topology and axis
majorants below are canonical finite suprema, not package data.  The only additional local premise
is the paper's noun-size condition for the three size-window opcodes. -/

include P in
/-- The state-tag injectivity already carried by the package rules out characteristic two. -/
theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro hzero
  have hnat : (2 : ℕ) = 0 :=
    P.stateTagChar
      (show (2 : ℕ) ∈ Set.Iic 11 by simp)
      (show (0 : ℕ) ∈ Set.Iic 11 by simp)
      (by simpa using hzero)
  omega

include P in
/-- **Fixed-field S7 feasibility receipt.**  For the package's own strategy,
failure union, census, atom range, noun-size bound and field `K`, false acceptance is bounded by the
canonical five-class workload divided by `|K|`.  No varying strategy or field family appears. -/
theorem fixedField_falseAcceptance_le (lmb : K) :
    |jointProbability
        (ProductionP8Containment.FalseAcceptanceSet P.strategy q Λ lmb)| ≤
      (ProductionP8Containment.workload P.strategy Λ
          (ProductionP8Containment.fixedTopologyWorkload P.strategy)
          (ProductionP8Containment.fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ) :=
  ProductionP8Containment.jointProbability_falseAcceptance_le
    P.two_ne_zero P.strategy lmb P.census q
    (ProductionP8Containment.fixedTopologyWorkload P.strategy)
    (ProductionP8Containment.fixedAxisWorkload P.strategy)
    (by simpa using P.sizeWindowBound)
    (ProductionP8Containment.topologyWorkload_le_fixedTopologyWorkload P.strategy)
    (ProductionP8Containment.templateAxisWorkload_le_fixedAxisWorkload P.strategy)
    (fun ω => P.containment ω lmb)

include P in
/-- The same fixed-field bound in bits.  Unlike the old arbitrary-field `goldilocks_margin`, the
event and workload are the package's own.  The support inequality is explicit because the full
five-class workload is larger than the collision-only numerator used by the paper's concrete
`120`-bit example. -/
theorem fixedField_falseAcceptance_le_two_pow_neg
    (lmb : K) (b : ℕ)
    (hsupport :
      ProductionP8Containment.workload P.strategy Λ
          (ProductionP8Containment.fixedTopologyWorkload P.strategy)
          (ProductionP8Containment.fixedAxisWorkload P.strategy) * 2 ^ b ≤
        Fintype.card K) :
    |jointProbability
        (ProductionP8Containment.FalseAcceptanceSet P.strategy q Λ lmb)| ≤
      1 / 2 ^ b := by
  refine (P.fixedField_falseAcceptance_le lmb).trans ?_
  have hcard : (0 : ℝ) < (Fintype.card K : ℝ) := by positivity
  have hpow : (0 : ℝ) < 2 ^ b := by positivity
  have hreal :
      (ProductionP8Containment.workload P.strategy Λ
          (ProductionP8Containment.fixedTopologyWorkload P.strategy)
          (ProductionP8Containment.fixedAxisWorkload P.strategy) : ℝ) *
          2 ^ b ≤
        (Fintype.card K : ℝ) := by
    exact_mod_cast hsupport
  rw [div_le_div_iff₀ hcard hpow]
  linarith

/-! ### S8: package-indexed exact monolithic cost -/

/-- **S8 fingerprint.**  Read off the two named chips' own `.w` / `.e`. -/
theorem fingerprint :
    (P.compRAP.w, P.memRAP.w, P.compRAP.e)
      = CompleteProductionCost.strictPaperG10Fingerprint := by
  rw [P.comp_is_named, P.mem_is_named]
  exact constructed_fingerprint_eq_strictG10 P.basis P.chalVal P.pubVal P.orbit P.Hc P.Hm

/-- **S8 shape.**  Widths, extension degree, max degree and round counts of the two named chips. -/
theorem chip_shape :
    P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧ P.compRAP.e = 3 ∧ P.memRAP.e = 3 ∧
      P.compRAP.d = 4 ∧ P.memRAP.d = 4 ∧ P.compRAP.k = 2 ∧ P.memRAP.k = 1 := by
  rw [P.comp_is_named, P.mem_is_named]
  exact ⟨(RAP_NockCompIO_width_e3 P.basis P.chalVal P.pubVal P.orbit P.Hc).1,
    (RAP_NockMemIO_width_e3 P.basis P.chalVal P.pubVal P.orbit P.Hm).1,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **S8 rows, compute.**  The named chip's row domain is the shared
execution's compute-row count. -/
theorem comp_rows : P.compRAP.H.card = P.objects.cfg.compRows := by
  rw [P.comp_is_named]
  exact RAP_NockCompIO_rows P.basis P.chalVal P.pubVal P.orbit P.Hc P.objects.exec P.Hc_card

/-- **S8 rows, memory.**  Under the exact `recordCountBalance`
residual, the named chip's row domain is the shared execution's exact memory budget. -/
theorem mem_rows :
    P.memRAP.H.card
      = RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec := by
  rw [P.mem_is_named]
  exact RAP_NockMemIO_rows P.basis P.chalVal P.pubVal P.orbit P.Hm
    P.recordCountBalance P.Hm_card

/-- **Strict package-indexed S8 claim.**  The cost slot is tied to `P`'s
two named monolithic RAPs: their exact fingerprint and chip metadata, the actual expanded
transition-gate lists (`87/88`) with equalities to the paper formulas, and the shared execution's
exact `N` / `M + 2L` row budgets. -/
structure StrictCostRealization : Prop where
  fingerprint :
    (P.compRAP.w, P.memRAP.w, P.compRAP.e)
      = CompleteProductionCost.strictPaperG10Fingerprint
  chip_shape :
    P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧ P.compRAP.e = 3 ∧ P.memRAP.e = 3 ∧
      P.compRAP.d = 4 ∧ P.memRAP.d = 4 ∧ P.compRAP.k = 2 ∧ P.memRAP.k = 1
  compute_transition_gates :
    ((compTemplate F).transitionGates P.basis).length = 87 ∧
      ((compTemplate F).transitionGates P.basis).length =
        Nock.NockVM.comp_io_deg4_gates 3
  memory_transition_gates :
    ((memTemplate F).transitionGates P.basis).length = 88 ∧
      ((memTemplate F).transitionGates P.basis).length =
        Nock.NockVM.mem_io_deg4_gates 3
  compute_row_budget : P.compRAP.H.card = P.objects.cfg.compRows
  memory_row_budget :
    P.memRAP.H.card =
      RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec

/-- The package realizes its exact monolithic S8 claim from its named-chip and row-layout facts. -/
theorem strictCostRealization : P.StrictCostRealization where
  fingerprint := P.fingerprint
  chip_shape := P.chip_shape
  compute_transition_gates := RAP_NockCompIO_transition_gates_e3 P.basis
  memory_transition_gates := RAP_NockMemIO_transition_gates_e3 P.basis
  compute_row_budget := P.comp_rows
  memory_row_budget := P.mem_rows

/-! ### S1--S8: the structural bundle, at the shared challenges and IO bound -/

/-- **S1--S7 over the shared objects.**  The Tier-2 structural bundle of `Capstone.lean`, keyed by
the shared execution's own `α`, `β` and `Ksz` — not by free tag parameters.  S5 is the package's
exact monolithic-chip/row-domain/IO/walk proposition.  S6 is `CombinedCompletenessAt` at this same
dependent `cfg`/`exec`.  S7 is exactly `∀ λ, FixedFieldSoundnessClaim P.strategy q Λ λ` (one bound at every sampled
Form R `λ`), proved by the
package's same-event five-class union bound above. -/
@[reducible] def structural :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, ProductionP8Containment.FixedFieldSoundnessClaim P.strategy q Λ lmb)
      P.fixedField_falseAcceptance_le
      (StrictCostRealization P)
      P.strictCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      (StrictTwoRAPRealization P)
      P.strictTwoRAPRealization
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K)
      (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec)
      P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩ :=
  ⟨⟩


/-- With the `B29SemanticTemplate` residual supplied, `Def:RAP` satisfaction of
the constructed compute chip splits into its base-field half and the claimed Nock language on the
`𝕂` environment gathered from the very same committed base columns. -/
theorem comp_satisfies_iff_language
    (T : Fin (RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc).w → F[X]) :
    (RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc).Satisfies T
      ↔ ∀ x ∈ P.Hc,
          (∀ g ∈ (compTemplate F).baseTransition,
              g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
            ∧ (∀ g ∈ (compTemplate F).equalityChecks,
              g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
            ∧ P.compLanguage (gatherEnv P.basis ((compTemplate F).col0 3)
              (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal)) :=
  Nock.RedTeam.Batch29.b29_residual_closes_language (compTemplate F) P.compLanguage
    P.compSemanticTemplate rfl P.basis P.chalVal P.pubVal P.orbit P.Hc T

theorem mem_satisfies_iff_language
    (T : Fin (RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm).w → F[X]) :
    (RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm).Satisfies T
      ↔ ∀ x ∈ P.Hm,
          (∀ g ∈ (memTemplate F).baseTransition,
              g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
            ∧ (∀ g ∈ (memTemplate F).equalityChecks,
              g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
            ∧ P.memLanguage (gatherEnv P.basis ((memTemplate F).col0 3)
              (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal)) :=
  Nock.RedTeam.Batch29.b29_residual_closes_language (memTemplate F) P.memLanguage
    P.memSemanticTemplate rfl P.basis P.chalVal P.pubVal P.orbit P.Hm T

end StrictNockVMROMPackage

/-- Public package-indexed name for the strict S5 proposition. -/
abbrev StrictTwoRAPRealization {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
  StrictNockVMROMPackage.StrictTwoRAPRealization P

/-- Public package-indexed name for the strict S8 proposition. -/
abbrev StrictCostRealization {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ} (P : StrictNockVMROMPackage F K hOrb q Λ) : Prop :=
  StrictNockVMROMPackage.StrictCostRealization P

/-! ## 3. The honest conditional capstone -/

/-- **The paper's Theorem-5.4 statement, over one threaded package.**

Every field is a genuine clause of the paper plus the deployed `e = 3` cost fingerprint.
This is a *conditional* statement: it is inhabited exactly when a `StrictNockVMROMPackage` is, and
that in turn needs the open residuals listed in the package's docstring. -/
structure StrictThm54Statement {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ) where
  /-- **S1--S4 and exact S6/S7** at the shared execution's own challenges, IO bound,
  configuration, dependent execution, production strategy, false-acceptance event and workload. -/
  structural :
    VerifiableVMCompilation
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (nmrMEF F K) K 10 3
      (∀ lmb : K, ProductionP8Containment.FixedFieldSoundnessClaim P.strategy q Λ lmb)
      P.fixedField_falseAcceptance_le
      (StrictCostRealization P)
      P.strictCostRealization
      (CombinedCompletenessAt P.objects.cfg P.objects.exec)
      (exactChainedHasPerfectCompleteness F K P.objects.cfg P.objects.exec)
      (StrictTwoRAPRealization P)
      P.strictTwoRAPRealization
      (nock_uniqueMES F K _ _ _)
      (ExactChainedHasCanonicalRAP2 F K)
      (exactChainedHasCanonicalRAP2 F K)
      (OneHotRealization P.objects.cfg P.objects.exec)
      P.chained.oneHotRealization
      (DefTraversableRealization P.objects.cfg)
      (defTraversableRealization P.objects.cfg P.objects.exec.memoryRootCount_pos)
      ⟨⟨stmtOfExact P.objects.cfg P.objects.exec, P.perfect_completeness⟩⟩
  /-- **S5.**  The verification really is by the two *named* constructed chips. -/
  named_raps :
    P.compRAP = RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc ∧
      P.memRAP = RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm
  /-- **S5.** -/
  comp_language :
    ∀ T : Fin (RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc).w → F[X],
      (RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc).Satisfies T
        ↔ ∀ x ∈ P.Hc,
            (∀ g ∈ (compTemplate F).baseTransition,
                g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
              ∧ (∀ g ∈ (compTemplate F).equalityChecks,
                g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
              ∧ P.compLanguage (gatherEnv P.basis ((compTemplate F).col0 3)
                (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal))
  /-- **S5, memory chip.** -/
  mem_language :
    ∀ T : Fin (RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm).w → F[X],
      (RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm).Satisfies T
        ↔ ∀ x ∈ P.Hm,
            (∀ g ∈ (memTemplate F).baseTransition,
                g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
              ∧ (∀ g ∈ (memTemplate F).equalityChecks,
                g.eval (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal) = 0)
              ∧ P.memLanguage (gatherEnv P.basis ((memTemplate F).col0 3)
                (Reify.envOfTrace T P.orbit.ω x P.chalVal P.pubVal))
  /-- **S5 / shared IO.**  The record-level IO language holds of the shared execution's own derived
  request/response records (Packet C). -/
  shared_io : IO.LIO P.objects.cfg.Ksz P.objects.reqRecs P.objects.respRecs
  /-- Forward top-level language witness at the shared tag. -/
  perfect_completeness :
    Language
      (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
      (stmtOfExact P.objects.cfg P.objects.exec)
  /-- **S7 (arbitrary prover).**  Accepting coins outside the counted failure union reach the
  genuine target. -/
  containment :
    ∀ (ω : JointCoins K) (lmb : K), P.strategy.Accepts ω lmb →
      ω ∉ ProductionP8Containment.FailureUnion P.strategy P.census lmb →
        ProductionP8Containment.GenuineTargetAt P.strategy q Λ ω lmb
  /-- **S7 (walk).**  Both walk soundness bounds of the shared table/walk row family. -/
  walk_bounds :
    P.computeWalkBadRatio ≤ P.computeWalkBound ∧
      P.memoryWalkBadRatio ≤ P.memoryWalkBound
  /-- **S7.**  False acceptance of this package's own
  verifier and failure union is bounded by its canonical five-class workload over its own `K`. -/
  fixed_field_soundness :
    ∀ lmb : K, |jointProbability
        (ProductionP8Containment.FalseAcceptanceSet P.strategy q Λ lmb)| ≤
      (ProductionP8Containment.workload P.strategy Λ
          (ProductionP8Containment.fixedTopologyWorkload P.strategy)
          (ProductionP8Containment.fixedAxisWorkload P.strategy) : ℝ) /
        (Fintype.card K : ℝ)
  /-- **S7 (same event, bit form).**  Any supported bit margin applies to the exact event above.
  This deliberately does not transfer the collision-only `120`-bit example of the paper to the
  larger five-class production workload. -/
  fixed_field_bits :
    ∀ (lmb : K) (b : ℕ),
      ProductionP8Containment.workload P.strategy Λ
          (ProductionP8Containment.fixedTopologyWorkload P.strategy)
          (ProductionP8Containment.fixedAxisWorkload P.strategy) * 2 ^ b ≤
        Fintype.card K →
      |jointProbability
          (ProductionP8Containment.FalseAcceptanceSet P.strategy q Λ lmb)| ≤
        1 / 2 ^ b
  /-- **S8.**  The deployed `e = 3` fingerprint of the two named chips. -/
  fingerprint :
    (P.compRAP.w, P.memRAP.w, P.compRAP.e)
      = CompleteProductionCost.strictPaperG10Fingerprint
  /-- **S8.**  Widths, degree and rounds. -/
  chip_shape :
    P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧ P.compRAP.e = 3 ∧ P.memRAP.e = 3 ∧
      P.compRAP.d = 4 ∧ P.memRAP.d = 4 ∧ P.compRAP.k = 2 ∧ P.memRAP.k = 1
  /-- **S8.**  The two row budgets `N` and `M + 2L`, over the shared execution. -/
  row_budgets :
    P.compRAP.H.card = P.objects.cfg.compRows ∧
      P.memRAP.H.card
        = RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec

/-- **PACKET F1 CAPSTONE — the honest conditional Theorem 5.4.**

Given the package — hence given its explicitly named open residuals `shapeMatch`, `rowFrame`,
`slotSemantics`, `compSemanticTemplate`, `memSemanticTemplate`, `recordCountBalance` and
`sizeWindowBound` —
the full S1--S8 statement holds over ONE threaded execution with the two constructed `199`/`196`
chips.  Every hypothesis of every clause is a field of `P`; nothing is assumed on the side, and the
unconditional Theorem 5.4 is *not* claimed. -/
def strictNockVMROM_of_package {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ) :
    StrictThm54Statement P where
  structural := P.structural
  named_raps := ⟨P.comp_is_named, P.mem_is_named⟩
  comp_language := P.comp_satisfies_iff_language
  mem_language := P.mem_satisfies_iff_language
  shared_io := P.io_language
  perfect_completeness := P.perfect_completeness
  containment := P.containment
  walk_bounds := ⟨P.computeWalk_bound, P.memoryWalk_bound⟩
  fixed_field_soundness := P.fixedField_falseAcceptance_le
  fixed_field_bits := P.fixedField_falseAcceptance_le_two_pow_neg
  fingerprint := P.fingerprint
  chip_shape := P.chip_shape
  row_budgets := ⟨P.comp_rows, P.mem_rows⟩

/-! ## 4. Threading receipts -/

section Receipts

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb q Λ : ℕ}
  (P : StrictNockVMROMPackage F K hOrb q Λ)

/-- **Receipt: one execution.**  The honest specialization of the arbitrary-prover verifier, the
shared table/walk row family, and the two IO record lists all reduce to the single
`⟨objects.cfg, objects.exec⟩`; there is no second execution anywhere in the package. -/
theorem package_single_execution :
    specializedProblem P.verifier.raw.timestamp P.honestSeed P.honestSeed_ne P.honestAlpha
        P.objects.cfg.challenges.lam = ⟨P.objects.cfg, P.objects.exec⟩ ∧
      P.walkFamily.problem = ⟨P.objects.cfg, P.objects.exec⟩ ∧
      P.objects.reqRecs = P.objects.exec.derivedRequestIO ∧
      P.objects.respRecs = P.objects.exec.derivedResponseIO ∧
      P.ioStrategy.records.requests = P.objects.exec.derivedRequestIO ∧
      P.ioStrategy.records.responses = P.objects.exec.derivedResponseIO ∧
      StrictReleaseContract P.objects.cfg P.objects.exec P.objects.reqRecs P.objects.respRecs :=
  ⟨P.honest_specialization, P.walkFamily_problem, P.objects.req_eq_derived,
    P.objects.resp_eq_derived, P.io_requests.trans P.objects.req_eq_derived,
    P.io_responses.trans P.objects.resp_eq_derived,
    strictThreadedObjects_satisfy_contract P.objects⟩

/-- **Receipt: the two chips are the named constructed RAPs**, over one basis, one orbit and one
base field, with the row domains sized by the shared execution. -/
theorem package_uses_named_raps :
    P.compRAP = RAP_NockCompIO P.basis P.chalVal P.pubVal P.orbit P.Hc ∧
      P.memRAP = RAP_NockMemIO P.basis P.chalVal P.pubVal P.orbit P.Hm ∧
      P.Hc.card = P.objects.exec.computeRows.length ∧
      P.Hm.card = P.objects.exec.memoryRows.length ∧
      P.compRAP.H.card = P.objects.cfg.compRows ∧
      P.memRAP.H.card
        = RowLayout.memoryM P.objects.exec + 2 * RowLayout.memoryL P.objects.exec :=
  ⟨P.comp_is_named, P.mem_is_named, P.Hc_card, P.Hm_card, P.comp_rows, P.mem_rows⟩

/-- **Receipt: the `(199, 196, 3)` fingerprint.** -/
theorem package_fingerprint_eq_strictG10 :
    (P.compRAP.w, P.memRAP.w, P.compRAP.e)
        = CompleteProductionCost.strictPaperG10Fingerprint ∧
      P.compRAP.w = 199 ∧ P.memRAP.w = 196 ∧ P.compRAP.e = 3 :=
  ⟨P.fingerprint, P.chip_shape.1, P.chip_shape.2.1, P.chip_shape.2.2.1⟩

/-- **Receipt: completeness is the FORWARD direction only.**  The package's S6 clause is
`perfect_completeness_is_forward`, and the unrestricted reverse language projection is still
refuted, so no reverse bridge slipped into the capstone. -/
theorem package_perfect_completeness_is_forward (r : (nmrMEF F K).Rec) :
    Language
        (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz)
        (stmtOfExact P.objects.cfg P.objects.exec) ∧
      ¬ ∀ x : Stmt F K,
          Language
            (Tag F K P.objects.cfg.challenges.α P.objects.cfg.challenges.β P.objects.cfg.Ksz) x →
          ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
            ChainedSemanticExactLanguage cfg exec ∧ stmtOfExact cfg exec = x :=
  ⟨P.perfect_completeness,
    unrestricted_reverse_still_false P.objects.cfg.challenges.α P.objects.cfg.challenges.β
      P.one_le_Ksz r⟩

/-- **Receipt: the residuals really are fields.**  Projecting them out of the package is the whole
proof — which is the point: the capstone is conditional on exactly these objects. -/
theorem package_residuals_are_fields :
    (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        ExecTreeShapeMatchesAt P.commitment
          (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ (z : K) (hz : z ≠ 0) (α lmb : K),
        RowFrameChecksAt z P.commitment
          (specializedProblem P.verifier.raw.timestamp z hz α lmb).exec) ∧
      (∀ s ∈ computeSkeletonRows P.commitment.skeleton, SkeletonSlotSemantics s) ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (compTemplate F) P.compLanguage ∧
      Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (memTemplate F) P.memLanguage ∧
      RowLayout.RecordCountBalanced P.objects.exec ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy P.commitment.skeleton Λ :=
  ⟨P.shapeMatch, P.rowFrame, P.slotSemantics, P.compSemanticTemplate, P.memSemanticTemplate,
    P.recordCountBalance, P.sizeWindowBound⟩

/-- **Non-vacuity, stated honestly: the package is inhabited ONLY under the residuals.**

No concrete small-field witness is exhibited, and none is fabricated: `slotSemantics` is the honest
memory reconstruction of a genuine Nock execution, while `sizeWindowBound` is the fixed skeleton's
local noun-size condition.  What is compiled here is the converse direction, which makes the
capstone conditional rather than an overclaim: every inhabitant hands back every residual. -/
theorem package_nonempty_only_under_residuals
    (h : Nonempty (StrictNockVMROMPackage F K hOrb q Λ)) :
    ∃ (C : SkeletonCommitment) (cfg : ExactConfig F K) (exec : ExactExecution cfg)
      (Lc Lm : Nock.Reified.Env K → Prop),
      (∀ s ∈ computeSkeletonRows C.skeleton, SkeletonSlotSemantics s) ∧
        RowLayout.RecordCountBalanced exec ∧
        Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (compTemplate F) Lc ∧
        Nock.RedTeam.Batch29.B29SemanticTemplate (K := K) (memTemplate F) Lm ∧
        SizeWindowCounting.SizeWindowNounsBoundedBy C.skeleton Λ :=
  h.elim fun Q =>
    ⟨Q.commitment, Q.objects.cfg, Q.objects.exec, Q.compLanguage,
      Q.memLanguage, Q.slotSemantics, Q.recordCountBalance, Q.compSemanticTemplate,
      Q.memSemanticTemplate, Q.sizeWindowBound⟩

end Receipts

end

end StrictPackage
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strategy
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strategy_skeleton
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strategy_verifier
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.one_le_Ksz
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.structural
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.perfect_completeness
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.io_language
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.binds
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.computeWalk_bound
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.memoryWalk_bound
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.StrictTwoRAPRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strictTwoRAPRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.containment
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.two_ne_zero
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fixedField_falseAcceptance_le
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fixedField_falseAcceptance_le_two_pow_neg
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.StrictCostRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.strictCostRealization
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.comp_satisfies_iff_language
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.mem_satisfies_iff_language
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.fingerprint
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.chip_shape
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.comp_rows
#print axioms Nock.NockVMROM.Thm54.StrictPackage.StrictNockVMROMPackage.mem_rows
#print axioms Nock.NockVMROM.Thm54.StrictPackage.strictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.StrictPackage.package_single_execution
#print axioms Nock.NockVMROM.Thm54.StrictPackage.package_uses_named_raps
#print axioms Nock.NockVMROM.Thm54.StrictPackage.package_fingerprint_eq_strictG10
#print axioms Nock.NockVMROM.Thm54.StrictPackage.package_perfect_completeness_is_forward
#print axioms Nock.NockVMROM.Thm54.StrictPackage.package_residuals_are_fields
#print axioms Nock.NockVMROM.Thm54.StrictPackage.package_nonempty_only_under_residuals
