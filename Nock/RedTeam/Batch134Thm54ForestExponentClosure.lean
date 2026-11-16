import Nock.NockVMROM.Thm54

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Different context from the prover. **No carrier
field is added**, no production mathematics is edited, and no named premise of the released capstone
is weakened. Nothing here describes the paper construction as defective.

The earlier analysis claims `ForestExponentOrder` is CLOSED at the consumed (pointwise-in-`D`) quantifier via the
canonical stamp `normData`, with the docstring "same execution, same committed skeleton and the
*same published memory rows* as `D`".  This module measures that claim.

## §1. What `normData` preserves, and what it moves

* The **execution rows** are `MemoryNode.row`, projected by `Data.memory_rows` onto
  `E.exec.memoryForest`.  `normData` leaves them **literally unchanged**
  (`b134_normData_execution_rows_identical`), together with the committed skeleton
  (`b134_normData_skeleton_identical`) and the specialised execution
  (`b134_normData_same_execution`).  The earlier docstring is correct at this reading.
* The **published committed template rows** are `MemoryRowTemplate`, i.e. `renderMemoryTemplate z n = ⟨n.stamp, …⟩`. These carry the committed Nat `recordExponent`, and
  they are exactly what the verifier reads: `packageOf_committedTemplate` is `rfl` onto
  `D.executionTemplate z`, and `alphaFreeAxisStructureCheck` / `noWrapCheck` decide on that object. `normData` **does** move them whenever `0 < orderOf α` and some committed exponent is at least
  `orderOf α`. Over a finite `K` the guard is just
  `α ≠ 0`, so the moving case is the whole live regime.)  The movement is compiled on the live F73
  fixture against the earlier second commitment
  (`b134_f73_normData_moves_the_published_template`): the wrapped F73 commitment publishes read
  exponent `10`, its canonical stamp publishes `1`, so the two committed templates are distinct
  objects.

So the normalisation is *not* invisible in the commitment in general. It is invisible exactly where
the paper says it should be: `b134_normData_invisible_under_window` compiles that if `D` already
satisfies the uniqueness window (the paper, which the paper's `N, L ∈ negl(K)` is
what supplies), then the canonical stamp changes nothing the α-free check can see — every published
read and verify exponent is returned unchanged. Outside the window, `normData D` is a *different* commitment of the same execution.

## §2. How the closure composes

`packageOf D` depends on `D` only through `commitmentResidualOfArrays_of_char D hgt`, so
`packageOf (normData D)` is a genuine `OptimizedFullStrictNockVMROMPackage` and the consumed capstone
applies to it unchanged (`b134_capstone_applies_to_the_normalised_package`).  The honest shape of the
closure is therefore existential over commitments of one execution
(`b134_closure_is_existential_over_commitments`): for every honest execution with `α ≠ 0` there
*exists* a commitment — same execution, same skeleton, same execution rows — whose package accepts
the whole honest fibre with no window hypothesis.  It is not the statement that the package built
from an arbitrary *supplied* `D` accepts; the earlier `no_universal_forestExponentOrder` still forbids
that, and the earlier analysis does not claim it.

## §3. Non-vacuity, at the two-service quantifier the earlier analysis actually needs

The earlier analysis compiled the live `∀ a g` acceptance only at F73, where its own §B derivation does **not**
apply (single served lookup) and `α ≠ 0` comes from the fixture's `α = 4`.  The two-service route
had no compiled live acceptance.  `b134_f97_unconditional_fibre_accepts` supplies it: on the released
capstone's F97 two-serviced-root fixture, with the pre-existing commitment `dataM` and pre-existing
`inputsM`, production fibre acceptance holds for **all** `a g` with no hypothesis on `α` at all — the
residual is discharged from the execution's held fields.

## §4. `α ≠ 0`, re-derived

`b134_alpha_ne_zero_of_two_services` re-derives the earlier §B independently: the "a `Nodup` list whose
entries are all equal has length `≤ 1`" step is re-proved by direct case analysis rather than through
`toFinset`, and the service/exponent chain is rebuilt from the held fields
`ServedMemoryTrace.Service.timestamp`, `Service.request_mem` and
`ExactServedMemoryTrace.timestampPowersNodup`.  Only
`rawRequest_ts_eq_zero_of_alpha_zero` (the `Vcomp` / `memBlk` line-number pinning, the paper) is taken from the prover artifact.  The hypothesis carries
no side condition on `α`, and `forestServiceExponents` is a projection of held fields alone
(`b134_two_service_hypothesis_reads_only_held_fields`).

-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch134

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
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §1a. What the canonical stamp preserves -/

/-- **The execution rows are literally `D`'s.**  `reExpNode` touches only `stamp.recordExponent`, and
`MemoryNode.row` does not see it. -- the paper -/
theorem b134_normData_execution_rows_identical {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).memoryNodes.map (mapNTree MemoryNode.row) =
      D.memoryNodes.map (mapNTree MemoryNode.row) := by
  rw [(normData D).memory_rows, D.memory_rows]

/-- …and so is the committed skeleton. -/
theorem b134_normData_skeleton_identical {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).skeleton = D.skeleton :=
  normData_skeleton D

/-- …and the honest sample still returns the supplied execution. -/
theorem b134_normData_same_execution {E : BuildableNockExecution F K} (D : Data E) :
    ((normData D).executionTemplate E.cfg.challenges.z).specialize E.cfg.challenges.α E.cfg.challenges.lam = E.exec :=
  normData_honest_exec D

/-- The compute half of the commitment is untouched, on the nose. -/
theorem b134_normData_computeNodes_identical {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).computeNodes = D.computeNodes := rfl

/-! ## §1b. What the canonical stamp moves: the published committed template

The verifier reads `committedTemplate … = D.executionTemplate z` (`packageOf_committedTemplate`,
`rfl`), whose memory forest is `D.memoryNodes.map (mapNTree (renderMemoryTemplate z))` — and
`renderMemoryTemplate z n` carries `n.stamp`, hence the committed Nat exponent. -/


theorem b134_verifier_reads_the_data_template {E : BuildableNockExecution F K}
    [Fintype F] [DecidableEq F] (D : Data E) (hgt : 11 < ringChar K) (I : Inputs E)
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E := by later_seed_zeros)
    (hord : 2 ≤ E.cfg.compRows →
      E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows →
      E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    committedTemplate (packageOf D hgt I hprl hmore hord hordM hrows hgenF hF).strategy.verifier
        E.cfg.challenges.z D.honestSeed_ne =
      D.executionTemplate E.cfg.challenges.z := rfl

/-- …and the published template row carries the committed Nat exponent. -/
theorem b134_published_row_carries_the_exponent (z : K) (n : MemoryNode K) :
    (renderMemoryTemplate z n).timestamp.recordExponent = n.stamp.recordExponent := rfl

/-- A relabelling that fixes every read and verify exponent of an axis tree is the identity on it. -/
theorem b134_reindexAxisTree_id_of_fixed (f : ℕ → ℕ) :
    ∀ t : MTree K, (∀ e ∈ readExps t, f e = e) → (∀ e ∈ verifyExps t, f e = e) →
      reindexAxisTree f t = t := by
  intro t
  induction t with
  | halt => intro _ _; rfl
  | decompose l r ihl ihr =>
      intro hr hv
      rw [reindexAxisTree, ihl (fun e he => hr e (by simp [readExps, he]))
          (fun e he => hv e (by simp [verifyExps, he])),
        ihr (fun e he => hr e (by simp [readExps, he]))
          (fun e he => hv e (by simp [verifyExps, he]))]
  | read e c ih =>
      intro hr hv
      rw [reindexAxisTree, hr e (by simp [readExps]),
        ih (fun x hx => hr x (by simp [readExps, hx])) (fun x hx => hv x (by simp [verifyExps, hx]))]
  | verify e a c ih =>
      intro hr hv
      rw [reindexAxisTree, hv e (by simp [verifyExps]),
        ih (fun x hx => hr x (by simp [readExps, hx])) (fun x hx => hv x (by simp [verifyExps, hx]))]

/-- **The canonical stamp is invisible exactly in the paper's regime.**  If the supplied commitment
already satisfies the uniqueness window (the paper, supplied by the paper's
`N, L ∈ negl(K)`), then `normData` returns every published read and verify exponent unchanged: the
α-free object the verifier decides on is the same tree.  So the stamp is a genuine canonical
representative there, not a repair. -- the paper -/
theorem b134_normData_invisible_under_window {E : BuildableNockExecution F K} (D : Data E)
    (hw : ForestExponentOrder (D.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α)
    (i : Fin (configTemplateOf E E.cfg.challenges.z).kMem) :
    alphaFreeRoot ((normData D).executionTemplate E.cfg.challenges.z) i =
      alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i := by
  rw [show ((normData D).executionTemplate E.cfg.challenges.z) =
      ((reExpData (fun e => e % orderOf E.cfg.challenges.α)
        (fun e => pow_mod_orderOf E.cfg.challenges.α e) D).executionTemplate
          E.cfg.challenges.z) from rfl]
  rw [alphaFreeRoot_reExpData]
  exact b134_reindexAxisTree_id_of_fixed _ _
    (fun e he => Nat.mod_eq_of_lt (hw.1 i e he))
    (fun e he => Nat.mod_eq_of_lt (hw.2 i e he))

/-! ## §1c. …and it genuinely moves the published template off that regime -/

end

namespace Concrete

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.AxisBridge
open Nock.AxisBatching
open ConcreteStrictPackage
open BuildableConcrete
open HonestCommitment.Concrete

noncomputable section

local instance : Fact (Nat.Prime 73) := concrete_prime73
noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73: dummy halt at index 0, serving root at index 1 (`kMem = 2`). -/
private theorem data73_serving_lt :
    1 < (configTemplateOf concreteExecution
      concreteExecution.cfg.challenges.z).kMem := by
  simp [configTemplateOf, BuildableConcrete.concreteExecution,
    ConcreteStrictPackage.cfg]

/-- The earlier second commitment of the F73 execution. -/
def wrapped73 : Data concreteExecution := wrapDataExponents data73

/-- The wrapped F73 commitment publishes read exponent `1 + orderOf α = 10` at the
serving root (index 1; index 0 is the dummy halt). -/

theorem b134_f73_wrapped_publishes_ten :
    readExps (alphaFreeRoot
        (wrapped73.executionTemplate concreteExecution.cfg.challenges.z)
        ⟨1, data73_serving_lt⟩) = [10] := by
  rw [show wrapped73 = wrapDataExponents data73 from rfl, alphaFreeRoot_wrapExponents,
    readExps_reindexAxisTree, ForestExponentWindow.Concrete.data73_alphaFreeRoot_exps.1]
  simp [ForestExponentOrderClosure.Concrete.f73_orderOf_alpha]

/-- Its canonical stamp publishes `1` at the serving root. -/

theorem b134_f73_normalised_wrapped_publishes_one :
    readExps (alphaFreeRoot
        ((normData wrapped73).executionTemplate concreteExecution.cfg.challenges.z)
        ⟨1, data73_serving_lt⟩) = [1] := by
  rw [show ((normData wrapped73).executionTemplate concreteExecution.cfg.challenges.z) =
      ((reExpData (fun e => e % orderOf concreteExecution.cfg.challenges.α)
        (fun e => pow_mod_orderOf concreteExecution.cfg.challenges.α e)
          wrapped73).executionTemplate concreteExecution.cfg.challenges.z) from rfl]
  rw [alphaFreeRoot_reExpData, readExps_reindexAxisTree, b134_f73_wrapped_publishes_ten]
  simp [ForestExponentOrderClosure.Concrete.f73_orderOf_alpha]

/-- It is invisible only under the window
(`b134_normData_invisible_under_window`), which `wrapped73` violates by construction.
-- -/
theorem b134_f73_normData_moves_the_published_template :
    (normData wrapped73).executionTemplate concreteExecution.cfg.challenges.z ≠
      wrapped73.executionTemplate concreteExecution.cfg.challenges.z := by
  intro h
  have h1 := b134_f73_normalised_wrapped_publishes_one
  rw [h, b134_f73_wrapped_publishes_ten] at h1
  simp at h1

/-- **Sharpness disclosure, compiled at the level §B's hypothesis actually lives at.**  The earlier analysis's
`f73_serves_one_lookup` states the *committed template's* read exponents are `[1]`; the two-service
hypothesis is about the *served trace*.  Here the served count itself is computed: F73's
`ExactServedMemoryTrace` carries exactly one service, so `2 ≤ (forestServiceExponents E).length` is
genuinely unavailable there and the residual the earlier analysis discloses is real.
-- -/
theorem b134_f73_serves_exactly_one_lookup :
    (forestServiceExponents concreteExecution).length = 1 := by
  -- F73: dummy halt (0 services) + one serving root with one service.
  simp [ForestExponentOrderClosure.forestServiceExponents,
    BuildableConcrete.concreteExecution, BuildableConcrete.concreteServedMemoryTrace,
    BuildableConcrete.concreteServedMemoryRoots, ServedMemoryTrace.RootTrace.exponents,
    ConcreteStrictPackage.cfg, List.finRange, BuildableConcrete.concreteDummyServedRoot,
    BuildableConcrete.concreteReadServedRoot] <;> rfl

/-- The pre-existing F73 commitment is already canonical at the α-free root the no-wrap check reads,
so at F73 the stamp returns every published read and verify exponent unchanged.  "No-op" is licensed
at that object only — this is `alphaFreeRoot` equality per root index, not `MemoryRowTemplate` forest
equality.  Dummy-wired through `package73Of_forestExponentOrder` (Form R leftover).
-- -/
theorem b134_f73_normData_is_a_noop_on_data73
    (horder : ForestExponentOrder
      (data73.executionTemplate concreteExecution.cfg.challenges.z)
      concreteExecution.cfg.challenges.α)
    (i : Fin (configTemplateOf concreteExecution concreteExecution.cfg.challenges.z).kMem) :
    alphaFreeRoot ((normData data73).executionTemplate concreteExecution.cfg.challenges.z) i =
      alphaFreeRoot (data73.executionTemplate concreteExecution.cfg.challenges.z) i :=
  b134_normData_invisible_under_window data73
    (GenericHonestPackage.Concrete.package73Of_forestExponentOrder horder) i

end

end Concrete

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## §2. How the closure composes downstream -/

/-- The consumed capstone applies to the normalised package unchanged: nothing downstream of
`packageOf` needs the package to have been built from a *supplied* `D`.
-- -/
theorem b134_capstone_applies_to_the_normalised_package {E : BuildableNockExecution F K}
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
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (packageOf (normData D) hgt I hprl hmore hord hordM hrows hgenF hF) :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package _ hax hbasis hwidth

/-- **The honest shape of the closure.**  For every honest execution with `α ≠ 0` there *exists* a
commitment of that execution — same skeleton, same execution rows — whose production package accepts
the whole honest fibre with no window hypothesis.  This is existential over commitments, not
universal: the earlier `no_universal_forestExponentOrder` is untouched.
-- -/
theorem b134_closure_is_existential_over_commitments {E : BuildableNockExecution F K}
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
    ∃ (D' : Data E) (hgenD' : GeneratedField.ClaimGenerated K D'.skeleton.publicClaim D'.Λ),
      D'.skeleton = D.skeleton ∧
        D'.memoryNodes.map (mapNTree MemoryNode.row) =
          D.memoryNodes.map (mapNTree MemoryNode.row) ∧
        (∀ a g : K, (packageOf D' hgt I hprl hmore hord hordM hrows hgenD' hF).strategy.Accepts (honestCoin E a g)
          E.cfg.challenges.lam) :=
  ⟨normData D, ForestExponentOrderClosure.normData_claimGenerated D hgenF,
    b134_normData_skeleton_identical D, b134_normData_execution_rows_identical D,
    normalised_package_fibre_accepts_of_ne_zero D hgt I hprl hmore hord hordM hrows hgenF hF hα⟩


theorem b134_headline_is_the_real_fibre_acceptance {E : BuildableNockExecution F K}
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
    (hservices : 2 ≤ (forestServiceExponents E).length) :
    ∀ a g : K,
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  normalised_package_fibre_accepts_of_two_services D hgt I hprl hmore hord hordM hrows hgenF hF hservices

/-! ## §4. `α ≠ 0`, re-derived independently -/

/-- Independent re-proof of the counting step: a `Nodup` list all of whose entries are one fixed
value has length at most one.  Direct case analysis, not `toFinset`. -/
theorem b134_nodup_all_eq_length_le_one {A : Type} (l : List A) (a : A)
    (hnd : l.Nodup) (h : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [_] => simp
  | x :: y :: t =>
      exfalso
      rw [List.nodup_cons] at hnd
      have hxy : x ≠ y := by
        intro hc
        exact hnd.1 (by simp [hc])
      exact hxy ((h x (by simp)).trans (h y (by simp)).symm)

/-- The two-service hypothesis is a statement about already-held fields only: the served exponent
multiset is the flatMap of `E.memoryTrace.roots i`'s service exponents.
-- -/
theorem b134_two_service_hypothesis_reads_only_held_fields (E : BuildableNockExecution F K) :
    forestServiceExponents E =
      (List.finRange E.cfg.kMem).flatMap
        (fun i => (E.memoryTrace.roots i).services.map ServedMemoryTrace.Service.exponent) :=
  rfl

/-- Independent re-derivation of the earlier §B's exponent positivity, from the held closed form
`ts = α^i` and the `Vcomp`/`memBlk` line-number pinning. -/

theorem b134_service_exponent_pos (E : BuildableNockExecution F K)
    (hα : E.cfg.challenges.α = 0) (s : ServedMemoryTrace.Service E.cfg E.execA) :
    0 < s.exponent := by
  rcases Nat.eq_zero_or_pos s.exponent with h0 | h
  · exfalso
    have hts : s.record.ts = 0 :=
      rawRequest_ts_eq_zero_of_alpha_zero E hα
        (by rw [← ForestExponentOrderClosure.execA_rawRequests E]; exact s.request_mem)
    have hclosed := s.timestamp
    rw [hts, h0, pow_zero] at hclosed
    exact zero_ne_one hclosed
  · exact h

/-- **Independent re-derivation of the earlier §B.**  Any supplied execution serving at least two memory
lookups forces `α ≠ 0`, from held fields alone and with no hypothesis on `α`.
-- -/
theorem b134_alpha_ne_zero_of_two_services (E : BuildableNockExecution F K)
    (h : 2 ≤ (forestServiceExponents E).length) :
    E.cfg.challenges.α ≠ 0 := by
  intro hα
  have hnd : ((forestServiceExponents E).map
      (fun e => E.cfg.challenges.α ^ e)).Nodup := by
    rw [← forestTimestampPowers_eq]
    exact E.memoryTrace.timestampPowersNodup
  have hall : ∀ x ∈ (forestServiceExponents E).map
      (fun e => E.cfg.challenges.α ^ e), x = (0 : K) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have hepos : 0 < e := by
      rw [forestServiceExponents, List.mem_flatMap] at he
      obtain ⟨i, _, hei⟩ := he
      rw [ServedMemoryTrace.RootTrace.exponents, List.mem_map] at hei
      obtain ⟨s, _, rfl⟩ := hei
      exact b134_service_exponent_pos E hα s
    rw [hα, zero_pow (by omega : e ≠ 0)]
  have hlen := b134_nodup_all_eq_length_le_one _ (0 : K) hnd hall
  rw [List.length_map] at hlen
  omega

/-- (The
equation itself is proof-irrelevant; its content is that the two *types* coincide, so no weakening
crept into the re-derivation.) -/
theorem b134_agrees_with_ao112 (E : BuildableNockExecution F K)
    (h : 2 ≤ (forestServiceExponents E).length) :
    b134_alpha_ne_zero_of_two_services E h = alpha_ne_zero_of_two_services E h := rfl

/-- Sharpness, re-checked: at one served lookup the held fields cannot exclude `α = 0`, because a
singleton timestamp multiset is `Nodup` for every `α`.  So the residual disclosed by the earlier analysis is real.
-- -/
theorem b134_single_lookup_cannot_exclude_zero (α : K) (e : ℕ) :
    ([e].map (fun j => α ^ j)).Nodup := by simp

/-! ## §6. The counted bad event, measured against the repo idiom

The earlier §C calls `zeroTimestampChallengeEvent` "the repo's existing idiom
(`JointSoundness.zeroSeedFailureEvent`) reused verbatim in shape".  The two are at **different
layers**: `zeroSeedFailureEvent : Finset (JointCoins K)` is a coin-space event of card `|K|³` and is
a summand of `ProductionP8Containment.FailureUnion`, whereas `zeroTimestampChallengeEvent : Finset K`
is a set of *field* values of card `1` and is wired into nothing.  Both are density `1/|K|` once put
at the same layer, and that is all the "`1/|K|`" figure means: a `Finset` cardinality ratio, **not**
a probability measure.  No probabilistic soundness statement is claimed by the earlier analysis and none is
derived here. -/

/-- The earlier bad set is a set of field values, of card `1`. -- the paper -/
theorem b134_ao112_event_card :
    (ForestExponentOrderClosure.zeroTimestampChallengeEvent : Finset K).card = 1 :=
  ForestExponentOrderClosure.zeroTimestampChallengeEvent_card

/-- The repo idiom it cites is a **coin-space** event, of card `|K|³`. -/
theorem b134_repo_idiom_card :
    (zeroSeedFailureEvent : Finset (JointCoins K)).card =
      Fintype.card K ^ 3 :=
  zeroSeedFailureEvent_card

/-- Put at the same layer, the earlier bad draw is the coin event `alphaM ω = 0`. -/
theorem b134_ao112_event_lifted_iff (ω : JointCoins K) :
    ω ∈ liftMemory (((ForestExponentOrderClosure.zeroTimestampChallengeEvent : Finset K) ×ˢ
        (Finset.univ : Finset K))) ↔ alphaM ω = 0 := by
  rw [mem_liftMemory_iff]
  simp [memoryCoins, ForestExponentOrderClosure.zeroTimestampChallengeEvent, eq_comm]

/-- …and there it has exactly the repo idiom's cardinality, i.e. the same `1/|K|` density.  This is
a counting statement about `Finset`s; it is not a probability measure and nothing probabilistic is
concluded from it. -- the paper -/
theorem b134_ao112_event_lifted_card :
    (liftMemory (((ForestExponentOrderClosure.zeroTimestampChallengeEvent : Finset K) ×ˢ
        (Finset.univ : Finset K)))).card = Fintype.card K ^ 3 := by
  rw [card_liftMemory]
  simp [ForestExponentOrderClosure.zeroTimestampChallengeEvent]
  ring

end

/-! ## §3. Non-vacuity at the two-service quantifier: the live F97 instance

The earlier analysis compiled `∀ a g` acceptance only at F73, where §B does *not* apply.  The released capstone's
F97 two-serviced-root fixture already carries a commitment (`MultiRootHonestCommitment.dataM`) and a
backend record (`MultiRootServedFixture.inputsM`), so the two-service route has a live instance. -/

namespace F97

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open MultiRootServedFixture
open MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

noncomputable section

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros multiRootExecution)

local instance prime97b : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97b : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

theorem b134_f97_char_gt_eleven : 11 < ringChar K97cubic := by
  rw [MultiRootServedFixture.ringChar_K97]; norm_num

/-- W3 stage 2: the tuple is a unit.  Previously stated as `challenge9 = 0`. -/
theorem b134_f97_h9 : inputsM.computeChallenges = default := by
  rw [inputsM_challenges]

/-- W3 stage 2: the tuple is a unit.  Previously stated as `challenge11 = 0`. -/
theorem b134_f97_h11 : inputsM.computeChallenges = default := by
  rw [inputsM_challenges]

/-- The live F97 execution serves three memory lookups. -- the paper -/
theorem b134_f97_three_services :
    2 ≤ (forestServiceExponents multiRootExecution).length := by
  rw [MultiRoot.multiRoot_forestServiceExponents_length]
  norm_num

/-- **Live non-vacuity of the earlier headline, at the quantifier it actually needs.**  Unconditional
`∀ a g` production fibre acceptance on the released capstone's F97 two-serviced-root fixture, for the
canonical stamp of the pre-existing commitment `dataM`, with **no hypothesis on `α`**: the residual is
discharged from the execution's own held fields.  This is the witness the earlier analysis did not compile.
-- -/
theorem b134_f97_unconditional_fibre_accepts :
    ∀ a g : K97cubic,
      (GenericHonestPackage.packageOf (normData dataM) b134_f97_char_gt_eleven inputsM
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (ForestExponentOrderClosure.normData_claimGenerated dataM MultiRootHonestCommitment.residualM_generated)
        MultiRootHonestCommitment.f97_primeField).strategy.Accepts (honestCoin multiRootExecution a g)
          multiRootExecution.cfg.challenges.lam :=
  normalised_package_fibre_accepts_of_two_services dataM b134_f97_char_gt_eleven inputsM
    pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
    MultiRootHonestCommitment.residualM_generated MultiRootHonestCommitment.f97_primeField b134_f97_three_services

/-- …and the consumed capstone holds of that very package. -- the paper -/
theorem b134_f97_capstone
    (hax : OptimizedComputeFinalTrace.FormRAxisBound
      (GenericHonestPackage.packageOf (normData dataM) b134_f97_char_gt_eleven inputsM
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (ForestExponentOrderClosure.normData_claimGenerated dataM MultiRootHonestCommitment.residualM_generated)
        MultiRootHonestCommitment.f97_primeField).optimized.sampled
      (GenericHonestPackage.packageOf (normData dataM) b134_f97_char_gt_eleven inputsM
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (ForestExponentOrderClosure.normData_claimGenerated dataM MultiRootHonestCommitment.residualM_generated)
        MultiRootHonestCommitment.f97_primeField).optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis
      (GenericHonestPackage.packageOf (normData dataM) b134_f97_char_gt_eleven inputsM
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (ForestExponentOrderClosure.normData_claimGenerated dataM MultiRootHonestCommitment.residualM_generated)
        MultiRootHonestCommitment.f97_primeField).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
      (GenericHonestPackage.packageOf (normData dataM) b134_f97_char_gt_eleven inputsM
        pairedRecordLayoutS hmoreM walkOrderM walkOrderMem rowsBoundM
        (ForestExponentOrderClosure.normData_claimGenerated dataM MultiRootHonestCommitment.residualM_generated)
        MultiRootHonestCommitment.f97_primeField) :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package _ hax hbasis hwidth

end

end F97

/-! ## §5. Invariants re-measured -/

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]


theorem b134_data_eta_unchanged {E : BuildableNockExecution F K} (D : Data E) :
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
theorem b134_buildable_execution_eta_unchanged (E : BuildableNockExecution F K) :
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

/-- The residual pair stays `11+1+2`, the fourteen-field partition of the released capstone statement
at F97 per `Batch91.exact_eleven_one_two_partition` (not reinterpreted). -/
theorem b134_residual_pair_still_eleven_one_two : 11 + 1 + 2 = 14 :=
  GenericHonestPackage.residual_pair_still_eleven_one_two_after_logup_inventory

/-- The earlier `∀ D'` refutation is not withdrawn and is re-exported here. -- the paper -/
theorem b134_forall_data_shape_still_refuted {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ∀ D' : Data E,
        ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  ForestExponentWindow.no_universal_forestExponentOrder D hne

/-- The consumed capstone and its route are untouched. -/
theorem b134_consumed_capstone_untouched [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth

end

#print axioms Nock.RedTeam.Batch134.b134_normData_execution_rows_identical
#print axioms Nock.RedTeam.Batch134.b134_normData_skeleton_identical
#print axioms Nock.RedTeam.Batch134.b134_normData_same_execution
#print axioms Nock.RedTeam.Batch134.b134_normData_computeNodes_identical
#print axioms Nock.RedTeam.Batch134.b134_verifier_reads_the_data_template
#print axioms Nock.RedTeam.Batch134.b134_published_row_carries_the_exponent
#print axioms Nock.RedTeam.Batch134.b134_reindexAxisTree_id_of_fixed
#print axioms Nock.RedTeam.Batch134.b134_normData_invisible_under_window
#print axioms Nock.RedTeam.Batch134.Concrete.wrapped73
#print axioms Nock.RedTeam.Batch134.Concrete.b134_f73_wrapped_publishes_ten
#print axioms Nock.RedTeam.Batch134.Concrete.b134_f73_normalised_wrapped_publishes_one
#print axioms Nock.RedTeam.Batch134.Concrete.b134_f73_normData_moves_the_published_template
#print axioms Nock.RedTeam.Batch134.Concrete.b134_f73_serves_exactly_one_lookup
#print axioms Nock.RedTeam.Batch134.Concrete.b134_f73_normData_is_a_noop_on_data73
#print axioms Nock.RedTeam.Batch134.b134_capstone_applies_to_the_normalised_package
#print axioms Nock.RedTeam.Batch134.b134_closure_is_existential_over_commitments
#print axioms Nock.RedTeam.Batch134.b134_headline_is_the_real_fibre_acceptance
#print axioms Nock.RedTeam.Batch134.b134_nodup_all_eq_length_le_one
#print axioms Nock.RedTeam.Batch134.b134_two_service_hypothesis_reads_only_held_fields
#print axioms Nock.RedTeam.Batch134.b134_service_exponent_pos
#print axioms Nock.RedTeam.Batch134.b134_alpha_ne_zero_of_two_services
#print axioms Nock.RedTeam.Batch134.b134_agrees_with_ao112
#print axioms Nock.RedTeam.Batch134.b134_single_lookup_cannot_exclude_zero
#print axioms Nock.RedTeam.Batch134.b134_ao112_event_card
#print axioms Nock.RedTeam.Batch134.b134_repo_idiom_card
#print axioms Nock.RedTeam.Batch134.b134_ao112_event_lifted_iff
#print axioms Nock.RedTeam.Batch134.b134_ao112_event_lifted_card
#print axioms Nock.RedTeam.Batch134.F97.b134_f97_char_gt_eleven
#print axioms Nock.RedTeam.Batch134.F97.b134_f97_h9
#print axioms Nock.RedTeam.Batch134.F97.b134_f97_h11
#print axioms Nock.RedTeam.Batch134.F97.b134_f97_three_services
#print axioms Nock.RedTeam.Batch134.F97.b134_f97_unconditional_fibre_accepts
#print axioms Nock.RedTeam.Batch134.F97.b134_f97_capstone
#print axioms Nock.RedTeam.Batch134.b134_data_eta_unchanged
#print axioms Nock.RedTeam.Batch134.b134_buildable_execution_eta_unchanged
#print axioms Nock.RedTeam.Batch134.b134_residual_pair_still_eleven_one_two
#print axioms Nock.RedTeam.Batch134.b134_forall_data_shape_still_refuted
#print axioms Nock.RedTeam.Batch134.b134_consumed_capstone_untouched

end Nock.RedTeam.Batch134
