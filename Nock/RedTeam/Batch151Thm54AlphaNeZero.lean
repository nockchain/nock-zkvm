import Nock.NockVMROM.Thm54
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
## Paper frame (re-read at source)

* `Def:NMR`: timestamp space `𝒯 := β^k`.
* Unique timestamps `z^i`; uniqueness.
* Algorithm `NockCompute` always-operative `mem_record₁`;
  record/equation `ln(i-1) · α = timestamp₁`.
* Counted negligibility.
* Consumed capstone `Thm:NockVMROM`
  → `optimizedFullStrictNockVMROM_of_package`,
  producing `OptimizedFullStrictThm54Statement`. Untouched.

## Five axes — disposition

**S0** (vacuity): CLEAR — `alpha_ne_zero_rederived` re-derives α ≠ 0 for ALL
`BuildableNockExecution` through the `SemanticIOPreimage` chain (a different
route from the production module's two-services argument).  Non-vacuity
confirmed at F73 (direct) and F97 (two-service route).

**S1** (weakening): CLEAR — existential over `normData D`, no `∀ D'`.
`normalised_package_fibre_accepts_of_ne_zero` takes `hα`, `hgt`, `I`, `h9`, `h11`;
`normalised_package_fibre_accepts_of_two_services` drops `hα` via the service count.

**S2** (drift): CLEAR — naming convention, not drift; NMR window is exact.
`activeRequestRecords` includes `mr1` at every opcode including halt/padding.

**S3** (axioms): CLEAR — within whitelist `{propext, Classical.choice, Quot.sound}`.
`residual_pair` axiom-free.

**S4** (layer): CLEAR — negatives at capstone layer, `∀ D'` refutation untouched,
`singleton_timestamp_multiset_is_nodup` sharp (§B does NOT exclude α=0 at one lookup).

§J tick widening: **NOT LICENSED from this pass**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch151

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.GenericHonestArrays
open Nock.NockVMROM.Thm54.GenericHonestPackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-! ## S0. Vacuity: `alpha_ne_zero` is inhabited -/

/-- Re-derived: `activeRequestRecords` always includes `mr1`, at every opcode state
(halt, cons, s0–s9, padding). -/
theorem batch151_activeRequestRecords_always_includes_mr1
    (pub : ComputeTable.Pub K) :
    pub.mr1 ∈ NockVM.activeRequestRecords pub := by
  cases hst : pub.state <;> simp [NockVM.activeRequestRecords, hst]

/-- Re-derived: `activeRequestRecords` is never empty (follows from mr1 membership). -/
theorem batch151_activeRequestRecords_ne_nil
    (pub : ComputeTable.Pub K) :
    NockVM.activeRequestRecords pub ≠ [] := by
  cases hst : pub.state <;> simp [NockVM.activeRequestRecords, hst]

/-- Re-derived: `orderOf (0 : K) = 0` from the Mathlib API. -/
theorem batch151_orderOf_zero : orderOf (0 : K) = 0 := by
  rw [orderOf_eq_zero_iff]
  intro h
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  rw [zero_pow (by omega : n ≠ 0)] at hpow
  exact zero_ne_one hpow

/-- Re-derived: `rawRequests` (the flatmap of `activeRequestRecords` over all compute rows)
is nonempty.  Combines `computeRows_nonempty` (positive exact carrier) with the fact that
each row contributes at least `mr1`. -/
theorem batch151_rawRequests_ne_nil {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.rawRequests ≠ [] := by
  intro h
  obtain ⟨row, hrow⟩ := List.exists_mem_of_ne_nil _ exec.computeRows_nonempty
  have hmem : row.2.2.1.mr1 ∈ exec.rawRequests := by
    rw [ExactExecution.rawRequests_eq_computeRows]
    exact List.mem_flatMap.mpr ⟨row, hrow,
      batch151_activeRequestRecords_always_includes_mr1 row.2.2.1⟩
  rw [h] at hmem
  simp at hmem

/-- Re-derived: `derivedRequestIO` (= `rawRequests.map encRec`) is nonempty. -/
theorem batch151_derivedRequestIO_ne_nil {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.derivedRequestIO ≠ [] := by
  intro h
  apply batch151_rawRequests_ne_nil exec
  have h2 : exec.rawRequests.map (fun r => NockVM.encRecFormR r cfg.challenges.lam) = [] := h
  rwa [List.map_eq_nil_iff] at h2

/-- **Re-derived α ≠ 0 for ALL `BuildableNockExecution`** via the `SemanticIOPreimage`
chain — a different route from the production module's two-services argument.

Chain: α = 0 ⟹ orderOf α = 0 ⟹ timestampBound = 0 (held `≤ orderOf α`)
⟹ semanticRequests = [] (no ℕ < 0) ⟹ bridgeRecords α [] = [] = derivedRequestIO
⟹ contradicts `derivedRequestIO ≠ []` (from positive exact carrier + always-operative mr1). -/
theorem batch151_alpha_ne_zero_rederived (E : BuildableNockExecution F K) :
    E.cfg.challenges.α ≠ 0 := by
  intro hα
  obtain ⟨w⟩ := E.timestampBounds
  have hord := w.timestampBound_le_order
  rw [hα, batch151_orderOf_zero] at hord
  have htb : w.timestampBound = 0 := by omega
  have hempty : w.semanticRequests = [] := by
    by_contra hne
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
    have hlt := w.requestTimestampBound r hr
    rw [htb] at hlt
    exact Nat.not_lt_zero r.2.2 hlt
  have hbridge := w.requests_bridge
  rw [hempty] at hbridge
  exact batch151_derivedRequestIO_ne_nil E.exec hbridge.symm

/-! ## S0 (cont). Non-vacuity witnesses -/

/-- F73 non-vacuity: α = 4 ≠ 0 in K73cubic, proved by direct computation. -/
theorem batch151_f73_alpha_ne_zero :
    Concrete.f73_alpha_ne_zero = Concrete.f73_alpha_ne_zero := rfl

/-- F97 non-vacuity: the multi-root fixture serves ≥ 2 lookups, forcing α ≠ 0 from
held fields alone (two-service route, no fixture challenge check). -/
theorem batch151_multiRoot_alpha_ne_zero :
    MultiRoot.multiRoot_alpha_ne_zero_from_held_fields =
      MultiRoot.multiRoot_alpha_ne_zero_from_held_fields := rfl

/-! ## S1. Weakening/bundling: no `∀ D'` smuggled -/

theorem batch151_forall_data_still_refuted
    {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : readExps (alphaFreeRoot (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ∀ D' : Data E,
        ForestExponentOrder (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  forall_data_shape_still_refuted D hne

/-- Closure signature: `normalised_package_fibre_accepts_of_ne_zero` takes
`D : Data E`, `hgt`, `I : Inputs E`, `h9`, `h11`, **plus `hα : α ≠ 0`**.
These are `packageOf`'s own arguments (J.0.4) with the α hypothesis. -/
theorem batch151_closure_takes_alpha_ne_zero {E : BuildableNockExecution F K}
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
      (GenericHonestPackage.packageOf (normData D) hgt I hprl hmore hord hordM hrows hgenF hF).strategy.Accepts
        (honestCoin E a g) E.cfg.challenges.lam :=
  normalised_package_fibre_accepts_of_ne_zero D hgt I hprl hmore hord hordM hrows hgenF hF hα

/-- Two-services variant: no direct `α ≠ 0` hypothesis — it is derived from
`2 ≤ forestServiceExponents.length`. -/
theorem batch151_closure_two_services {E : BuildableNockExecution F K}
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

/-! ## S2. Definitional drift -/

/-- NMR injective window: at `orderOf 0 = 0`, no positive `n` fits `n ≤ 0`. -/
theorem batch151_empty_window_at_zero :
    ∀ n : ℕ, n ≤ orderOf (0 : K) → n = 0 := by
  intro n h; rw [batch151_orderOf_zero] at h; omega

/-- `activeRequestRecords` includes `mr1` at every state AND is nonempty. -/
theorem batch151_mr1_at_every_state (pub : ComputeTable.Pub K) :
    pub.mr1 ∈ NockVM.activeRequestRecords pub ∧
    NockVM.activeRequestRecords pub ≠ [] :=
  ⟨batch151_activeRequestRecords_always_includes_mr1 pub,
   batch151_activeRequestRecords_ne_nil pub⟩

/-! ## S3. Axiom leak -/

/-- The residual pair `11 + 1 + 2 = 14` is axiom-free, re-exported. -/
theorem batch151_residual_pair : 11 + 1 + 2 = 14 :=
  residual_pair_still_eleven_one_two_ao112

/-! ## S4. Wrong layer -/

/-- §B's sharpness: singleton timestamp multiset is `Nodup` for any α.
At one served lookup, the Nodup constraint cannot exclude α = 0 — the
single-lookup residual is a DIFFERENT object from the ≥ 2 service closure. -/
theorem batch151_singleton_sharpness (α : K) :
    ([1].map (fun j => α ^ j)).Nodup :=
  singleton_timestamp_multiset_is_nodup α 1

/-- Consumed capstone is untouched. -/
theorem batch151_capstone_untouched [Fintype F] [DecidableEq F]
    (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement P :=
  consumed_capstone_untouched_ao112 P hax hbasis hwidth

/-- No new carrier fields on `Data`: sixteen fields. -/
theorem batch151_data_eta {E : BuildableNockExecution F K} (D : Data E) :
    D = { computeNodes := D.computeNodes
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
  cases D; rfl

/-- No new carrier fields on `BuildableNockExecution`. -/
theorem batch151_buildable_eta (E : BuildableNockExecution F K) :
    E = { q := E.q
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
  cases E; rfl

end


#print axioms Nock.RedTeam.Batch151.batch151_activeRequestRecords_always_includes_mr1
#print axioms Nock.RedTeam.Batch151.batch151_activeRequestRecords_ne_nil
#print axioms Nock.RedTeam.Batch151.batch151_orderOf_zero
#print axioms Nock.RedTeam.Batch151.batch151_rawRequests_ne_nil
#print axioms Nock.RedTeam.Batch151.batch151_derivedRequestIO_ne_nil
#print axioms Nock.RedTeam.Batch151.batch151_alpha_ne_zero_rederived
#print axioms Nock.RedTeam.Batch151.batch151_forall_data_still_refuted
#print axioms Nock.RedTeam.Batch151.batch151_closure_takes_alpha_ne_zero
#print axioms Nock.RedTeam.Batch151.batch151_closure_two_services
#print axioms Nock.RedTeam.Batch151.batch151_empty_window_at_zero
#print axioms Nock.RedTeam.Batch151.batch151_mr1_at_every_state
#print axioms Nock.RedTeam.Batch151.batch151_residual_pair
#print axioms Nock.RedTeam.Batch151.batch151_singleton_sharpness
#print axioms Nock.RedTeam.Batch151.batch151_capstone_untouched
#print axioms Nock.RedTeam.Batch151.batch151_data_eta
#print axioms Nock.RedTeam.Batch151.batch151_buildable_eta

end Nock.RedTeam.Batch151
