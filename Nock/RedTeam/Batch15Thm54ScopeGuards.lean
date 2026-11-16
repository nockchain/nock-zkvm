import Nock.RedTeam.Batch15Thm54SizeWindow
import Nock.NockVMROM.Thm54.RawJointSoundness
import Nock.NockVMROM.Thm54.NounRealization
import Nock.NockVMROM.Thm54.CompleteProductionCost
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.Walk37.PaperNames
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Each
guard below is a **regression receipt pinning the current scope boundary**; none of them closes the
corresponding gap, and none is an admissibility argument for paper Theorem 5.4.

* **(B) Raw versus production scope.**  The raw strategy types are data-only; the production
  strategy is a raw verifier *plus* `BareSemanticSupport`.  The receipts give the exact structural
  shape of both, show final acceptance is blind to the support, and show the genuine target is not.
* **(C) External semantic inputs.**  Served OP0/OP9 global-carry lookups and OP4 no-overflow are
  literal fields of the operational premises.  The re-exported `NounRealization` countermodel shows
  a production-accepted memory row whose active parent fingerprint has no noun preimage at all.
* **(G) Explicit cost budgets.**  The exact IO row count is derived
  separately and supplies no per-row field-operation constant.
* **(I) Nat `evalN` versus TeX field-modular OP4.**  `the paper` defines increment as
  `(1+n) mod p`, while `Nock.Reference.evalN` uses unbounded Nat successor.  Over the explicit
  five-element field `ZMod 5` the two disagree at the top atom `p - 1 = 4`, and agreement is
  recovered only under `IncrementNoOverflow` / a successful guarded run.
-/

namespace Nock.RedTeam

open scoped Classical
open Nock Nock.Walk Nock.Framework Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.CompleteProductionCost

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [charRing : CharP K (ringChar K)]

/-! ## Guard (B): raw data-only shape versus the semantically supported production type -/

/-- Exact structural shape of the arbitrary-prover raw strategy: a public claim, a seed
commitment function, and a post-coin walk response.  There is no fourth, semantic field. -/
theorem b15_rawP8Strategy_exact_shape
    (T : Thm54.RawP8Strategy F K (ringChar K)) :
    T =
      { claim := T.claim
        afterSeed := T.afterSeed
        afterCoins := T.afterCoins } :=
  rfl

/-- Exact structural shape of the template-fixed raw production strategy: a data-only staged
timestamp, an `alphaM`-phase commitment function, and a post-coin walk response. -/
theorem b15_templateRaw_strategy_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)) :
    V.raw =
      { timestamp := V.raw.timestamp
        afterAlphaM := V.raw.afterAlphaM
        afterCoins := V.raw.afterCoins } :=
  rfl

/-- Exact structural shape of the topology-enabled production verifier: the data-only raw strategy
plus phase-committed topology payload arrays.  Still no semantic field. -/
theorem b15_productionRawVerifier_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)) :
    V =
      { raw := V.raw
        topologyAfterAlphaM := V.topologyAfterAlphaM } :=
  rfl

theorem b15_productionStrategy_exact_shape
    (T : ProductionP8Containment.ProductionStrategy F K) :
    T =
      { verifier := T.verifier
        skeleton := T.skeleton
        publicClaim_eq := T.publicClaim_eq } :=
  rfl

/-- Exact structural shape of the honest semantic support: one pre-seed skeleton, the
public-claim equation, and the all-`alpha` `BindsAt` family. -/
theorem b15_bareSemanticSupport_exact_shape
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (S : ProductionP8Containment.BareSemanticSupport F K V) :
    S =
      { skeleton := S.skeleton
        publicClaim_eq := S.publicClaim_eq
        binds := S.binds } :=
  rfl

/-- Every object in the domain of the production soundness theorems factors as a raw verifier
together with a skeleton whose public claim is the verifier's.  (Before the split: verifier plus a
`BareSemanticSupport`; that factorisation now holds exactly for the honest strategies
`ProductionStrategy.ofBare S`.) -/
theorem b15_productionStrategy_is_verifier_plus_support
    (T : ProductionP8Containment.ProductionStrategy F K) :
    ∃ (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
      (sk : SemanticStrategy.SemanticSkeleton) (h : sk.publicClaim = V.raw.claim),
      T = { verifier := V, skeleton := sk, publicClaim_eq := h } :=
  ⟨T.verifier, T.skeleton, T.publicClaim_eq, rfl⟩

/-- The two explicit semantic obligations carried by every HONEST production strategy
(`ofBare S`), and by no raw strategy: the skeleton's public claim is the verifier's claim, and the
skeleton binds the specialized config/execution at *every* nonzero seed and *every* sampled
`alphaM`.  A general strategy carries only the first; binding is supplied per coin
(`BindsAtCoin`). -/
theorem b15_production_domain_carries_semantic_obligations
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (S : ProductionP8Containment.BareSemanticSupport F K V) :
    (ProductionP8Containment.ProductionStrategy.ofBare S).skeleton.publicClaim =
        (ProductionP8Containment.ProductionStrategy.ofBare S).verifier.raw.claim ∧
      (ProductionP8Containment.ProductionStrategy.ofBare S).BindsAll :=
  ⟨S.publicClaim_eq, ProductionP8Containment.ProductionStrategy.ofBare_bindsAll S⟩

/-! ## Guard (C): served OP0/OP9 lookups are external inputs -/

/-- The two served lookups are literal fields of the seed-independent operational core. -/
theorem b15_external_semantic_inputs_are_premise_fields
    (s : BoundSemanticTrace.RowSkeleton)
    (core : BoundSemanticTrace.SkeletonOperationalCore s) :
    (s.state = .s0 →
        GlobalCarryAxis.ServedLookup
          (GlobalCarryRecognizer.ofNoun s.subject 1)
          (P8Census.skeletonMemoryAxis s 1) s.evaluation) ∧
      (s.state = .s9 →
        GlobalCarryAxis.ServedLookup
          (GlobalCarryRecognizer.ofNoun
            (P8Census.skeletonSubformula s 0 .result) 1)
          (P8Census.skeletonMemoryAxis s 2)
          (P8Census.skeletonSubformula s 1 .formula)) :=
  ⟨core.s0_served, core.s9_served⟩

/-- The two skeleton memory-record equations feeding those served lookups are also literal fields,
so the whole OP0/OP9 lookup package is external input. -/
theorem b15_served_lookup_record_equations_are_premise_fields
    (s : BoundSemanticTrace.RowSkeleton)
    (core : BoundSemanticTrace.SkeletonOperationalCore s)
    (h0 : s.state = .s0) (h9 : s.state = .s9) :
    ((s.memoryRecord (1 : Fin 3)
          (by simp [h0, Nock.Framework.recordCount])).root = s.subject ∧
        (s.memoryRecord (1 : Fin 3)
          (by simp [h0, Nock.Framework.recordCount])).child = s.evaluation) ∧
      ((s.memoryRecord (2 : Fin 3)
          (by simp [h9, Nock.Framework.recordCount])).root =
            P8Census.skeletonSubformula s 0 .result ∧
        (s.memoryRecord (2 : Fin 3)
          (by simp [h9, Nock.Framework.recordCount])).child =
            P8Census.skeletonSubformula s 1 .formula) :=
  ⟨core.s0_record h0, core.s9_record h9⟩

omit charRing in
/-- The operational core is seed-independent: one core plus the size-window facts recovered outside
the counted fifth event yields the row-local premises at *any* seed.  This is the exact interface
through which the external inputs reach the scheduling proof. -/
theorem b15_operational_core_serves_every_seed
    {q : ℕ} (s : BoundSemanticTrace.RowSkeleton)
    (hq : q = ringChar K)
    (core : BoundSemanticTrace.SkeletonOperationalCore s)
    (z : K) (windows : BoundSemanticTrace.SkeletonSizeWindowPremises z s) :
    BoundSemanticTrace.SkeletonOperationalPremises q z s :=
  BoundSemanticTrace.SkeletonOperationalPremises.ofCoreAndWindows hq core windows

/-- Re-exported countermodel: a memory row that the production row verifier **accepts** and whose
tree is a genuine production `Fmem` leaf, yet whose active parent fingerprint has **no** noun
preimage under the global-carry encoding — so it cannot inhabit the exact-row noun predicate.
Acceptance alone therefore never supplies a noun preimage; noun realization has to be supplied
externally, exactly as the served lookups are. -/
theorem b15_accepted_memory_row_has_no_noun_preimage (q : ℕ) :
    MemoryPublicRowAccepted NounRealizationCounterRegression.badRow ∧
      RVT (MemoryTable.Fmem (K := NounRealizationCounterRegression.K289))
        NounRealizationCounterRegression.badTree ∧
      (¬ ∃ n : Noun,
        GlobalCarryRecognizer.enc (1 : NounRealizationCounterRegression.K289) n =
          NounRealizationCounterRegression.badFP) ∧
      (¬ FPRealized (1 : NounRealizationCounterRegression.K289) q
        NounRealizationCounterRegression.badFP) ∧
      ¬ MemoryPublicRowNounRealization q NounRealizationCounterRegression.badRow :=
  ⟨NounRealizationCounterRegression.badRow_publicAccepted,
    NounRealizationCounterRegression.badTree_rvt,
    NounRealizationCounterRegression.badFP_no_noun_preimage,
    NounRealizationCounterRegression.badFP_not_realized q,
    NounRealizationCounterRegression.badRow_not_nounRealized q⟩

/-! ## Compiled theorems re-exported with their quantification domains on the record -/

/-- The compiled production false-acceptance probability theorem, re-exported so its strategy
argument type (`ProductionStrategy`, i.e. verifier *plus* `BareSemanticSupport`) is on the record
next to the raw shapes above. -/
noncomputable def b15_production_probability_over_supported_type :=
  @ProductionP8Containment.production_jointProbability_falseAcceptance_le

/-- The compiled raw forward-soundness theorem, whose strategy argument is the data-only
`RawP8Strategy`.  Its conclusion is `ForwardSoundnessAt`: table, walk, and IO facts only, with no
semantic binding and no noun-level target. -/
noncomputable def b15_raw_forward_soundness_over_raw_type :=
  @Thm54.RawP8Strategy.forwardSoundness_of_accepts

/-- The compiled containment theorem, re-exported so its explicit per-row operational-core
hypothesis is on the record as a premise rather than a consequence. -/
noncomputable def b15_containment_takes_operational_core_as_premise :=
  @ProductionP8Containment.accepted_outside_failureUnion

section DecEq

variable [DecidableEq K]

/-- Final production acceptance is *blind* to the semantic support: replacing the support while
keeping the raw verifier leaves the accepted set unchanged.  Acceptance is therefore a raw-strategy
predicate and cannot be the source of any semantic conclusion. -/
theorem b15_production_accepts_independent_of_semantic_support
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (A B : ProductionP8Containment.BareSemanticSupport F K V)
    (ω : JointCoins K) (lmb : K) :
    ProductionP8Containment.ProductionStrategy.Accepts
        (ProductionP8Containment.ProductionStrategy.ofBare A) ω lmb ↔
      ProductionP8Containment.ProductionStrategy.Accepts
        (ProductionP8Containment.ProductionStrategy.ofBare B) ω lmb :=
  Iff.rfl

end DecEq

variable [Fintype K] [DecidableEq K]

/-- The whole content of the extra semantic field is its skeleton: two supports over one verifier
are equal exactly when their skeletons are. -/
theorem b15_bare_support_content_is_exactly_its_skeleton
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (A B : ProductionP8Containment.BareSemanticSupport F K V) :
    A = B ↔ A.skeleton = B.skeleton :=
  ⟨fun h => by rw [h],
    ProductionP8Containment.bareSemanticSupport_no_proof_carrying_fields V A B⟩

omit [Fintype K] [DecidableEq K] in
/-- In contrast to acceptance, the genuine target *does* speak about the support's skeleton: a
genuine witness pins the skeleton's root compute labels to the verifier's public claim. -/
theorem b15_genuine_witness_speaks_about_support_skeleton
    (T : ProductionP8Containment.ProductionStrategy F K)
    (q Λ : ℕ) (z : K) (hz : z ≠ 0) (α lmb : K)
    (w : ProductionP8Containment.GenuineWitness T q Λ z hz α lmb) :
    T.skeleton.computeTree.label.subject = T.verifier.raw.claim.subject ∧
      T.skeleton.computeTree.label.formula = T.verifier.raw.claim.formula ∧
      T.skeleton.computeTree.label.evaluation = T.verifier.raw.claim.result :=
  w.rootPublicNouns

/-! ## Guard (G): the three operation budgets are caller-supplied, not derived -/

omit [Fintype K] [DecidableEq K] in
/-- Nothing in `T` or `omega` determines any of these budgets. -/
theorem b15_cost_budgets_are_recorded_caller_inputs
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    let c := CompleteProductionCost.completeProductionCostAt
      T ω lmb hz rootBound gateBound ioBound
    c.rootAxisPolynomialOperationBound = rootBound ∧
      c.legacyPublicGateOperationBound = gateBound ∧
      c.ioTraceConstructionOperationBound = ioBound ∧
      c.completeDeterministicOperationBound =
        c.topologyOperationBound + c.axisStructureOperationBound +
          rootBound + gateBound + ioBound :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [Fintype K] [DecidableEq K] in
/-- The recorded cost data determines the caller's three budgets, so they are genuinely stored
parameters and not abbreviations of derived quantities. -/
theorem b15_cost_record_determines_caller_budgets
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (root₁ gate₁ io₁ root₂ gate₂ io₂ : ℕ)
    (h : CompleteProductionCost.completeProductionCostAt T ω lmb hz root₁ gate₁ io₁ =
      CompleteProductionCost.completeProductionCostAt T ω lmb hz root₂ gate₂ io₂) :
    root₁ = root₂ ∧ gate₁ = gate₂ ∧ io₁ = io₂ :=
  ⟨congrArg
      CompleteProductionCost.CompleteProductionCostData.rootAxisPolynomialOperationBound h,
    ⟨congrArg
        CompleteProductionCost.CompleteProductionCostData.legacyPublicGateOperationBound h,
      congrArg
        CompleteProductionCost.CompleteProductionCostData.ioTraceConstructionOperationBound h⟩⟩

omit [Fintype K] [DecidableEq K] in
/-- The complete deterministic operation bound is strictly increasing in the caller's
root-polynomial budget.  A quantity derived from the verifier and the sampled coins could not move
with a free parameter, so this bound is conditional accounting. -/
theorem b15_complete_bound_strictly_increases_in_root_budget
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound d : ℕ) (hd : 0 < d) :
    (CompleteProductionCost.completeProductionCostAt T ω lmb hz rootBound gateBound ioBound
        ).completeDeterministicOperationBound <
      (CompleteProductionCost.completeProductionCostAt
        T ω lmb hz (rootBound + d) gateBound ioBound
        ).completeDeterministicOperationBound := by
  dsimp only [CompleteProductionCost.completeProductionCostAt]
  omega

omit [Fintype K] [DecidableEq K] in
theorem b15_complete_bound_strictly_increases_in_gate_budget
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound d : ℕ) (hd : 0 < d) :
    (CompleteProductionCost.completeProductionCostAt T ω lmb hz rootBound gateBound ioBound
        ).completeDeterministicOperationBound <
      (CompleteProductionCost.completeProductionCostAt
        T ω lmb hz rootBound (gateBound + d) ioBound
        ).completeDeterministicOperationBound := by
  dsimp only [CompleteProductionCost.completeProductionCostAt]
  omega

omit [Fintype K] [DecidableEq K] in
/-- The same strict dependence on the caller's IO-trace-construction budget. -/
theorem b15_complete_bound_strictly_increases_in_io_budget
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound d : ℕ) (hd : 0 < d) :
    (CompleteProductionCost.completeProductionCostAt T ω lmb hz rootBound gateBound ioBound
        ).completeDeterministicOperationBound <
      (CompleteProductionCost.completeProductionCostAt
        T ω lmb hz rootBound gateBound (ioBound + d)
        ).completeDeterministicOperationBound := by
  dsimp only [CompleteProductionCost.completeProductionCostAt]
  omega

/-- The cost certificate holds for **every** triple of budgets, including three zeroes. -/
theorem b15_cost_certificate_holds_at_zero_budgets
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0) :
    CompleteProductionCost.CompleteProductionCostCertificate T ω lmb hz 0 0 0
      (CompleteProductionCost.completeProductionCostAt T ω lmb hz 0 0 0) :=
  CompleteProductionCost.completeProductionCost_certificate T ω lmb hz 0 0 0

omit [Fintype K] [DecidableEq K] in
/-- Derived versus supplied, side by side: the *number* of root-boundary polynomial evaluations is
exactly the committed `kMem` and is derived, while the *operation* budget for performing them is
the caller's parameter. -/
theorem b15_root_evaluation_count_derived_budget_supplied
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    let c := CompleteProductionCost.completeProductionCostAt
      T ω lmb hz rootBound gateBound ioBound
    c.rootAxisPolynomialEvaluations =
        (T.verifier.raw.timestamp.afterSeed ⟨nprSeed ω, hz⟩).configTemplate.kMem ∧
      c.rootAxisPolynomialOperationBound = rootBound :=
  ⟨rfl, rfl⟩

omit [Fintype K] [DecidableEq K] in
/-- The number of verifier-reconstructed IO rows is the exact sum of the request and response
`records + 1` domains, while the operation budget for constructing those rows is supplied by the
caller.  The exact row count therefore does not invent a per-row field-operation constant. -/
theorem b15_io_row_count_derived_budget_supplied
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    let c := CompleteProductionCost.completeProductionCostAt
      T ω lmb hz rootBound gateBound ioBound
    c.verifierReconstructedIORows =
        ((T.verifier.familyAt ω lmb hz).exec.derivedRequestIO.length + 1) +
          ((T.verifier.familyAt ω lmb hz).exec.derivedResponseIO.length + 1) ∧
      c.ioTraceConstructionOperationBound = ioBound :=
  ⟨rfl, rfl⟩

/-! ## Retained boundary: strict G10 fingerprint -/

/-- Retained strict-G10 numerical scope guard: the production AIR fingerprint is `188/78` at
`e = 1`, the strict paper G10 package is `199/196` at `e = 3`, and the two differ. -/
theorem b15_production_fingerprint_ne_strict_g10
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    CompleteProductionCost.completeProductionAIRFingerprint
        (CompleteProductionCost.completeProductionCostAt
          T ω lmb hz rootBound gateBound ioBound) = (188, 79, 1) ∧
      CompleteProductionCost.strictPaperG10Fingerprint = (199, 196, 3) ∧
      CompleteProductionCost.completeProductionAIRFingerprint
          (CompleteProductionCost.completeProductionCostAt
            T ω lmb hz rootBound gateBound ioBound) ≠
        CompleteProductionCost.strictPaperG10Fingerprint :=
  b14_production_fingerprint_ne_strict_g10 T ω lmb hz rootBound gateBound ioBound

end


noncomputable def b15_paper_alias_remains_forest :=
  @«Thm:NockVMROM:forest-control»

/-! ## Guard (I): TeX field-modular OP4 versus the Nat reference `evalN`

`the paper` defines `+(n) = (1 + n) mod p`, whereas `Nock.Reference.evalN` uses the
unbounded Nat successor `Noun.lus`.  Everything below is decided over the explicit five-element
field `ZMod 5`, the same small field already used for the axiom-clean witnesses in
`Batch8PolyION`. -/

section TexFieldOP4

/-- The explicit small prime used by the divergence witness. -/
abbrev texWitnessPrime : ℕ := 5

instance b15_fact_prime_five : Fact (Nat.Prime texWitnessPrime) := ⟨by norm_num⟩

/-- The witness really lives over a finite field of five elements, not merely over a modular
quotient: `ZMod 5` is a field and has exactly `5` elements. -/
theorem b15_texWitnessField_isField_card :
    IsField (ZMod texWitnessPrime) ∧ Fintype.card (ZMod texWitnessPrime) = 5 :=
  ⟨Field.toIsField (ZMod texWitnessPrime), by simp⟩

/-- The canonical representative computed by the modulus-`q` increment is exactly the value of the
TeX field increment `1 + n` taken in `ZMod q`. -/
theorem b15_lusFBy_eq_texFieldIncrement (n : ℕ) :
    FieldEmbedding.lusFBy texWitnessPrime (.atom n) =
      some (.atom (((n : ZMod texWitnessPrime) + 1).val)) := by
  simp only [FieldEmbedding.lusFBy, Option.some.injEq, Noun.atom.injEq]
  rw [← Nat.cast_one (R := ZMod texWitnessPrime), ← Nat.cast_add, ZMod.val_natCast]

/-- At the top of the field the TeX increment wraps to the zero element. -/
theorem b15_texFieldIncrement_wraps_at_top :
    (1 : ZMod texWitnessPrime) + ((4 : ℕ) : ZMod texWitnessPrime) = 0 := by
  decide

/-- The exact atom-level divergence at `p - 1 = 4`: the TeX field-modular increment yields the atom
`0`, the Nat reference `Noun.lus` yields the atom `5`, and these are different nouns. -/
theorem b15_texOP4_ne_natLus_at_top :
    FieldEmbedding.lusFBy texWitnessPrime (.atom 4) = some (.atom 0) ∧
      Noun.lus (.atom 4) = some (.atom 5) ∧
      FieldEmbedding.lusFBy texWitnessPrime (.atom 4) ≠ Noun.lus (.atom 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The source of the divergence, stated in the field: the two divergent atoms have the *same*
image in `ZMod 5` but are distinct natural numbers.  The field-modular semantics identifies them;
the Nat semantics of `evalN` does not. -/
theorem b15_divergent_atoms_collapse_only_in_the_field :
    ((5 : ℕ) : ZMod texWitnessPrime) = ((0 : ℕ) : ZMod texWitnessPrime) ∧
      (5 : ℕ) ≠ (0 : ℕ) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The formula `[4 [1 n]]`, i.e. `+(n)`: the smallest Nock formula whose only opcode work is one
OP4 increment, here of the literal `n`.  The operand is supplied by OP1 rather than by an OP0 axis
lookup because `Noun.slot` is defined by well-founded recursion and is therefore opaque to the
kernel; with OP1 the entire run is closed by kernel computation and `decide` suffices. -/
def b15_incrementFormula (n : ℕ) : Noun :=
  .cell (.atom 4) (.cell (.atom 1) (.atom n))

/-- Whole-evaluator divergence at the top atom: on the same subject and formula `+(4)`, the TeX
field-modular evaluator returns the atom `0` while the Nat reference `evalN` returns the atom `5`. -/
theorem b15_evalFBy_ne_evalN_at_top :
    FieldEmbedding.evalFBy texWitnessPrime 2 (.atom 0) (b15_incrementFormula 4) =
        some (.atom 0) ∧
      Nock.evalN 2 (.atom 0) (b15_incrementFormula 4) = some (.atom 5) ∧
      FieldEmbedding.evalFBy texWitnessPrime 2 (.atom 0) (b15_incrementFormula 4) ≠
        Nock.evalN 2 (.atom 0) (b15_incrementFormula 4) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The OP4 no-overflow premise is exactly what excludes the divergent point: it fails at the top
atom `4` and holds one step below. -/
theorem b15_incrementNoOverflow_fails_exactly_at_top :
    ¬ OpcodeSemantics.IncrementNoOverflow texWitnessPrime (.atom 4) ∧
      OpcodeSemantics.IncrementNoOverflow texWitnessPrime (.atom 3) := by
  constructor
  · show ¬ (4 + 1 < 5)
    omega
  · show 3 + 1 < 5
    omega

/-- The guarded evaluator crashes on exactly the divergent run, which is why a successful guarded
run is an honest (non-vacuous) no-overflow side condition. -/
theorem b15_guarded_run_crashes_at_top :
    FieldEmbedding.evalGBy texWitnessPrime 2 (.atom 0) (b15_incrementFormula 4) = none := by
  decide

/-- The surviving agreement direction over the same explicit field: for `5`-bounded inputs, a
successful guarded run forces the Nat reference and the TeX field-modular evaluator to agree. -/
theorem b15_noOverflow_agreement_over_texWitnessField
    {fuel : ℕ} {s f r : Noun}
    (hs : FieldEmbedding.BoundedBy texWitnessPrime s)
    (hf : FieldEmbedding.BoundedBy texWitnessPrime f)
    (hno : FieldEmbedding.evalGBy texWitnessPrime fuel s f = some r) :
    Nock.evalN fuel s f = some r ∧
      FieldEmbedding.evalFBy texWitnessPrime fuel s f = some r ∧
      FieldEmbedding.BoundedBy texWitnessPrime r :=
  FieldEmbedding.agreeBy texWitnessPrime (by norm_num) fuel s f r hs hf hno

/-- Concrete instance of the surviving direction one step below the boundary: the guarded run
succeeds and both evaluators return the atom `4`. -/
theorem b15_agreement_below_top :
    Nock.evalN 2 (.atom 0) (b15_incrementFormula 3) = some (.atom 4) ∧
      FieldEmbedding.evalFBy texWitnessPrime 2 (.atom 0) (b15_incrementFormula 3) =
        some (.atom 4) := by
  have hs : FieldEmbedding.BoundedBy texWitnessPrime (Noun.atom 0) := by
    norm_num
  have hf : FieldEmbedding.BoundedBy texWitnessPrime (b15_incrementFormula 3) := by
    norm_num [b15_incrementFormula]
  have hG :
      FieldEmbedding.evalGBy texWitnessPrime 2 (.atom 0) (b15_incrementFormula 3) =
        some (.atom 4) := by
    decide
  obtain ⟨hN, hF, -⟩ := b15_noOverflow_agreement_over_texWitnessField hs hf hG
  exact ⟨hN, hF⟩

end TexFieldOP4

#print axioms b15_rawP8Strategy_exact_shape
#print axioms b15_templateRaw_strategy_exact_shape
#print axioms b15_productionRawVerifier_exact_shape
#print axioms b15_productionStrategy_exact_shape
#print axioms b15_bareSemanticSupport_exact_shape
#print axioms b15_productionStrategy_is_verifier_plus_support
#print axioms b15_production_domain_carries_semantic_obligations
#print axioms b15_external_semantic_inputs_are_premise_fields
#print axioms b15_served_lookup_record_equations_are_premise_fields
#print axioms b15_operational_core_serves_every_seed
#print axioms b15_accepted_memory_row_has_no_noun_preimage
#print axioms b15_production_probability_over_supported_type
#print axioms b15_raw_forward_soundness_over_raw_type
#print axioms b15_containment_takes_operational_core_as_premise
#print axioms b15_production_accepts_independent_of_semantic_support
#print axioms b15_bare_support_content_is_exactly_its_skeleton
#print axioms b15_genuine_witness_speaks_about_support_skeleton
#print axioms b15_cost_budgets_are_recorded_caller_inputs
#print axioms b15_cost_record_determines_caller_budgets
#print axioms b15_complete_bound_strictly_increases_in_root_budget
#print axioms b15_complete_bound_strictly_increases_in_gate_budget
#print axioms b15_complete_bound_strictly_increases_in_io_budget
#print axioms b15_cost_certificate_holds_at_zero_budgets
#print axioms b15_root_evaluation_count_derived_budget_supplied
#print axioms b15_io_row_count_derived_budget_supplied
#print axioms b15_production_fingerprint_ne_strict_g10
#print axioms b15_paper_alias_remains_forest
#print axioms texWitnessPrime
#print axioms b15_fact_prime_five
#print axioms b15_texWitnessField_isField_card
#print axioms b15_lusFBy_eq_texFieldIncrement
#print axioms b15_texFieldIncrement_wraps_at_top
#print axioms b15_texOP4_ne_natLus_at_top
#print axioms b15_divergent_atoms_collapse_only_in_the_field
#print axioms b15_incrementFormula
#print axioms b15_evalFBy_ne_evalN_at_top
#print axioms b15_incrementNoOverflow_fails_exactly_at_top
#print axioms b15_guarded_run_crashes_at_top
#print axioms b15_noOverflow_agreement_over_texWitnessField
#print axioms b15_agreement_below_top

end Nock.RedTeam
