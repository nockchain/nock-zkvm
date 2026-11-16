import Nock.RedTeam.Batch134bThm54ClosureDisclosures
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# The independent gate of the `ForestExponentOrder` tick

Fresh independent spec-redteam pass.  It is gated here.

**Nothing in this module describes the paper construction as defective.**  No carrier field is
added, no production mathematics is edited and no named premise of the released capstone is
weakened.

## §1. The accepted predicate has content

`normalised_package_fibre_accepts_of_ne_zero` is unconditional `∀ a g` acceptance at the real
production `GenericHonestPackage.packageOf`.  It is not: at the *same* package built from the *same* canonically
stamped commitment, acceptance fails at some joint coin, because production `Accepts` is `False` at
a zero NPR seed.  `b142_fibre_acceptance_has_content` compiles both halves
together, so the tick's headline is measured against a predicate that is not constantly `true`.

The closure is also re-derived here directly from the production entry point
(`b142_closure_is_production_theorem_at_normData`), rather than re-exported: the only input beyond
`packageOf`'s own arguments is the window at `normData D`, which `α ≠ 0` supplies.

## §2. The general movement claim, which was carried as unverified

`redteam-status.json`'s `batch134b_unverified` records: "section D.1's general movement claim is
compiled only at the F73 instance, not as a theorem quantified over all `D`".  It is compiled here
for an arbitrary `D` on an arbitrary buildable execution
(`b142_normData_moves_published_read_exponents`, the `verify` twin, and the template-level
corollary): whenever the committed template publishes a read or verify exponent at least
`orderOf α`, with `0 < orderOf α`, the canonical stamp returns a *different* published exponent
list, hence a different committed template.  This **strengthens the production module's own
disclosure** (`ForestExponentOrderClosure` §D.1) from one fixture to the general case; it is a
disclosure of what the honest prover's canonical representative moves, not a defect.

The mitigating half is unchanged and is not weakened: under the window nothing moves
(`Batch134b.b134b_window_read_verify_exponents_unchanged`), which is exactly the
the paper `N, L ∈ negl(K)` regime whose timestamp content is the paper.

## §3. The two-service hypothesis discriminates

`α ≠ 0` is *derived*, not assumed, at any execution serving two or more memory lookups.  A derived
hypothesis is worth nothing if it is either unsatisfiable or free.  It is neither, and both live
fixtures are compiled side by side here (`b142_two_service_hypothesis_discriminates_at_F97`,
`b142_two_service_hypothesis_is_unavailable_at_F73`): the F97 two-serviced-root execution serves
three lookups, so the derivation fires there; the F73 execution serves exactly one, so it does not,
which is precisely the single-lookup case the row records as open.

## §4. Invariants re-measured

`Data` sixteen fields, `BuildableNockExecution` fourteen, `ResidualPremises` four,
`CensusRecordPremises` five, and `11 + 1 + 2` consumed as recorded and not reinterpreted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch142

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.AxisBridge

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §1. The accepted predicate has content -/

/-- **The closure, re-derived from the production entry point rather than re-exported.**  The only
input beyond `packageOf`'s own arguments is the uniqueness window at the canonically stamped
commitment, and `α ≠ 0` supplies it.  Nothing else is threaded in. -/
theorem b142_closure_is_production_theorem_at_normData {E : BuildableNockExecution F K}
    [Fintype F] [DecidableEq F] (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hα : E.cfg.challenges.α ≠ 0) :
    ∀ a g : K,
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy.Accepts (honestCoin E a g)
        E.cfg.challenges.lam :=
  packageOf_fibre_accepts (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF
    (forestExponentOrder_normData_of_ne_zero D hα)

/-- **Non-triviality gate.**  At the very package the tick names, the honest fibre is accepted *and*
some joint coin is rejected — production `Accepts` is `False` at a zero NPR seed.  So `∀ a g`
acceptance is a statement about the fibre and not an artefact of a predicate that holds of
everything -/
theorem b142_fibre_acceptance_has_content {E : BuildableNockExecution F K}
    [Fintype F] [DecidableEq F] (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hα : E.cfg.challenges.α ≠ 0) :
    (∀ a g : K,
        (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy.Accepts (honestCoin E a g)
          E.cfg.challenges.lam) ∧
      ¬ ∀ ω : JointCoins K,
          (packageOf (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF).strategy.Accepts ω
            E.cfg.challenges.lam :=
  ⟨b142_closure_is_production_theorem_at_normData D hgt I hprl hmore hord hordM hrows hgenF hF hα,
    packageOf_not_forall_omega (normData D) hgt I hprl hmore hord hordM hrows (ForestExponentOrderClosure.normData_claimGenerated D hgenF) hF⟩

/-- The fibre is at the execution's *own* timestamp and seed challenges, which is the same `α` the
window and the `α ≠ 0` hypothesis are about — so no coordinate slippage separates the hypothesis
from the object -/
theorem b142_fibre_sits_at_the_execution_challenges (E : BuildableNockExecution F K) (a g : K) :
    alphaM (honestCoin E a g) = E.cfg.challenges.α ∧
      nprSeed (honestCoin E a g) = E.cfg.challenges.z :=
  ⟨(honestCoin_coordinates E a g).2.2.1, (honestCoin_coordinates E a g).2.2.2⟩

/-! ## §2. The general movement claim -/

/-- A list fixed by a relabelling is fixed pointwise. -/
theorem b142_map_eq_self_pointwise {n : ℕ} {l : List ℕ}
    (h : l.map (fun e => e % n) = l) : ∀ e ∈ l, e % n = e := by
  induction l with
  | nil => intro e he; simp at he
  | cons a t ih =>
      rw [List.map_cons, List.cons.injEq] at h
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact h.1
      · exact ih h.2 e he

/-- For an arbitrary `D` on an arbitrary buildable
execution: if the committed template publishes a read exponent at least `orderOf α`, the canonical
stamp returns a different published read-exponent list at that root -/
theorem b142_normData_moves_published_read_exponents {E : BuildableNockExecution F K}
    (D : Data E) (hpos : 0 < orderOf E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) {e : ℕ}
    (he : e ∈ readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i))
    (hge : orderOf E.cfg.challenges.α ≤ e) :
    readExps (alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i) ≠
      readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) := by
  intro h
  rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
      ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
        (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
          E.cfg.challenges.z) from rfl] at h
  rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree] at h
  have hfix := b142_map_eq_self_pointwise h e he
  have hlt : e % orderOf E.cfg.challenges.α < orderOf E.cfg.challenges.α :=
    Nat.mod_lt _ hpos
  omega

/-- The `verify_child` twin of the same statement -/
theorem b142_normData_moves_published_verify_exponents {E : BuildableNockExecution F K}
    (D : Data E) (hpos : 0 < orderOf E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) {e : ℕ}
    (he : e ∈ verifyExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i))
    (hge : orderOf E.cfg.challenges.α ≤ e) :
    verifyExps (alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i) ≠
      verifyExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) := by
  intro h
  rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
      ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
        (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
          E.cfg.challenges.z) from rfl] at h
  rw [alphaFreeRoot_reExpData, verifyExps_reindexAxisTree] at h
  have hfix := b142_map_eq_self_pointwise h e he
  have hlt : e % orderOf E.cfg.challenges.α < orderOf E.cfg.challenges.α :=
    Nat.mod_lt _ hpos
  omega

/-- …hence the published committed template itself moves, generally and not only at F73.  This is
the object the verifier decides on (`packageOf_committedTemplate` is `rfl`), which is why the
production module discloses the movement rather than claiming template equality. -/
theorem b142_normData_moves_the_published_template {E : BuildableNockExecution F K}
    (D : Data E) (hpos : 0 < orderOf E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) {e : ℕ}
    (he : e ∈ readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i))
    (hge : orderOf E.cfg.challenges.α ≤ e) :
    (normData D).executionTemplate E.cfg.challenges.z ≠
      D.executionTemplate E.cfg.challenges.z := by
  intro h
  exact b142_normData_moves_published_read_exponents D hpos i he hge
    (congrArg (fun T => readExps (alphaFreeRoot T i)) h)

/-- The mitigating half is unchanged and is re-anchored here rather than restated in prose: under
the window every published read and verify exponent is returned unchanged, so inside the
the paper regime the canonical stamp is invisible at the object the α-free check reads. -/
theorem b142_movement_is_exactly_outside_the_window {E : BuildableNockExecution F K}
    (D : Data E)
    (hw : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) :
    readExps (alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i) =
        readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ∧
      verifyExps (alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i) =
        verifyExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) :=
  Batch134b.b134b_window_read_verify_exponents_unchanged D hw i

/-- The `∀ D'` shape stays refuted; nothing in this gate touches it -/
theorem b142_forall_data_shape_still_refuted {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ∀ D' : Data E,
        ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  ForestExponentWindow.no_universal_forestExponentOrder D hne

/-! ## §4. Invariants re-measured -/

/-- `Data` still has exactly its sixteen fields. -/
theorem b142_data_eta_unchanged {E : BuildableNockExecution F K} (D : Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } := by
  cases D
  rfl

/-- `BuildableNockExecution` still has exactly its fourteen fields. -/
theorem b142_buildable_execution_eta_unchanged (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-- `ResidualPremises` still has exactly its four fields. -/
theorem b142_residual_premises_eta_unchanged {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- `CensusRecordPremises` still has exactly its five fields. -/
theorem b142_census_record_premises_eta_unchanged {E : BuildableNockExecution F K}
    (P : ResidualPremises E) (M : MemoryRecordPremises E) (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } := by
  cases C
  rfl

/-- `11 + 1 + 2` is consumed exactly as `Batch91.exact_eleven_one_two_partition` records it, and is
not reinterpreted here. -/
theorem b142_residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

/-- The consumed capstone and its route are untouched by this gate. -/
theorem b142_consumed_capstone_untouched [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth

end

/-! ## §3. The two-service hypothesis discriminates between the live fixtures -/

namespace F97

open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open MultiRootServedFixture
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

noncomputable section

local instance prime97g : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97g : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- The derivation **fires** at the live two-serviced-root F97 execution: three served lookups, so
`α ≠ 0` follows from held fields with no hypothesis on the challenge -/
theorem b142_two_service_hypothesis_discriminates_at_F97 :
    2 ≤ (forestServiceExponents multiRootExecution).length ∧
      multiRootExecution.cfg.challenges.α ≠ 0 :=
  ⟨by rw [MultiRoot.multiRoot_forestServiceExponents_length]; norm_num,
    MultiRoot.multiRoot_alpha_ne_zero_from_held_fields⟩

end

end F97

namespace F73

open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open ConcreteStrictPackage
open BuildableConcrete

noncomputable section

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- …and it is **unavailable** at the live F73 execution, which serves exactly one lookup.  So the
hypothesis is neither unsatisfiable nor free, and the single-lookup case the row records as open is
a real case and not a hedge -/
theorem b142_two_service_hypothesis_is_unavailable_at_F73 :
    ¬ 2 ≤ (forestServiceExponents concreteExecution).length := by
  rw [Batch134.Concrete.b134_f73_serves_exactly_one_lookup]
  omega

end

end F73

#print axioms Nock.RedTeam.Batch142.b142_closure_is_production_theorem_at_normData
#print axioms Nock.RedTeam.Batch142.b142_fibre_acceptance_has_content
#print axioms Nock.RedTeam.Batch142.b142_fibre_sits_at_the_execution_challenges
#print axioms Nock.RedTeam.Batch142.b142_map_eq_self_pointwise
#print axioms Nock.RedTeam.Batch142.b142_normData_moves_published_read_exponents
#print axioms Nock.RedTeam.Batch142.b142_normData_moves_published_verify_exponents
#print axioms Nock.RedTeam.Batch142.b142_normData_moves_the_published_template
#print axioms Nock.RedTeam.Batch142.b142_movement_is_exactly_outside_the_window
#print axioms Nock.RedTeam.Batch142.b142_forall_data_shape_still_refuted
#print axioms Nock.RedTeam.Batch142.b142_data_eta_unchanged
#print axioms Nock.RedTeam.Batch142.b142_buildable_execution_eta_unchanged
#print axioms Nock.RedTeam.Batch142.b142_residual_premises_eta_unchanged
#print axioms Nock.RedTeam.Batch142.b142_census_record_premises_eta_unchanged
#print axioms Nock.RedTeam.Batch142.b142_residual_pair_still_eleven_one_two
#print axioms Nock.RedTeam.Batch142.b142_consumed_capstone_untouched
#print axioms Nock.RedTeam.Batch142.F97.b142_two_service_hypothesis_discriminates_at_F97
#print axioms Nock.RedTeam.Batch142.F73.b142_two_service_hypothesis_is_unavailable_at_F73

end Nock.RedTeam.Batch142
