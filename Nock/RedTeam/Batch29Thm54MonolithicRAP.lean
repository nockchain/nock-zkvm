/-
  Nock/RedTeam/Batch29Thm54MonolithicRAP.lean

  Locked facts:

  1. **The constructed values exist and are non-vacuous.**  A concrete pair over `𝔽₁₃` and the
     genuine cubic extension `GaloisField 13 3` type-checks, carries `e = 3`, and its `Def:RAP`
     generator has exact order `e·2^h = 12`.
  3. **Single field, single domain.**  Both chips are `Framework.RAP F` over the *same* base field,
     share `ω`, `β`, `e`, `h` and the row domain, and each chip's satisfaction is one quantification
     over one constraint index set and one row domain — not a conjunction over a segmented family
     (contrast the existing segmented object's `32` kind-indexed RAP evaluations).
  4. **The shape predicate has teeth**: the memory template is refuted as a compute shape, and a
     tampered width is refuted, so the fingerprint theorems are not vacuously about every template.
  5. **The old scoped inequality is preserved**: `b14_production_fingerprint_ne_strict_g10` (the
     `188/78` segmented object is not the strict G10 package) still holds, simultaneously with the
     new `(199, 196, 3)` equality — they are statements about two different objects.
  6. **The residual is named as a compiled artifact**: `B29SemanticTemplate` is exactly the missing
     hypothesis, and `b29_residual_closes_language` shows that supplying it closes the
     satisfaction ⟺ language equivalence with no further work.
-/

import Nock.NockVMROM.Thm54.StrictG10Cost
import Nock.RedTeam.Batch14Thm54Production

namespace Nock.RedTeam.Batch29

open Module
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MonolithicRAP

open scoped Polynomial

noncomputable section

/-! ## 1. The constructed values exist and are non-vacuous -/

/-- **Non-vacuity.**  Both named RAPs are inhabited at the paper's `e = 3`, over `𝔽₁₃` and a
genuine cubic extension of it. -/
theorem b29_constructed_pair_nonvacuous :
    Nonempty (RAP MonolithicRAP.G13) :=
  ⟨MonolithicRAP.concreteCompRAP⟩

/-- **The concrete `e = 3` pair carries the paper's fingerprint.** -/
theorem b29_concrete_fingerprint :
    MonolithicRAP.concreteCompRAP.w = 199 ∧ MonolithicRAP.concreteMemRAP.w = 196 ∧
      MonolithicRAP.concreteCompRAP.e = 3 ∧ MonolithicRAP.concreteMemRAP.e = 3 ∧
      MonolithicRAP.concreteCompRAP.d = 4 ∧ MonolithicRAP.concreteMemRAP.d = 4 ∧
      MonolithicRAP.concreteCompRAP.k = 2 ∧ MonolithicRAP.concreteMemRAP.k = 1 :=
  MonolithicRAP.concrete_fingerprint

/-- **The concrete pair's generator really has exact order `e·2^h`**, so
the orbit data is not metadata. -/
theorem b29_concrete_omega_order :
    orderOf MonolithicRAP.concreteCompRAP.ω
        = MonolithicRAP.concreteCompRAP.e * 2 ^ MonolithicRAP.concreteCompRAP.h ∧
      orderOf MonolithicRAP.concreteMemRAP.ω
        = MonolithicRAP.concreteMemRAP.e * 2 ^ MonolithicRAP.concreteMemRAP.h :=
  MonolithicRAP.concrete_omega_order

/-! ## 2. Generic `e = 3` fingerprint receipts -/

section Generic

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {h : ℕ} (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (Hc Hm : Finset F)

/-- **Width receipts**: `199` compute / `196` memory columns at `e = 3`, read
off the constructed `.w`, and matching the paper transcription defs. -/
theorem b29_widths :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).w = 199 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).w = 196 ∧
      (RAP_NockCompIO b chalVal pubVal orbit Hc).w = Nock.NockVM.comp_io_columns 3 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).w = Nock.NockVM.mem_io_columns 3 :=
  ⟨(RAP_NockCompIO_width_e3 b chalVal pubVal orbit Hc).1,
    (RAP_NockMemIO_width_e3 b chalVal pubVal orbit Hm).1,
    (RAP_NockCompIO_width_e3 b chalVal pubVal orbit Hc).2,
    (RAP_NockMemIO_width_e3 b chalVal pubVal orbit Hm).2⟩

/-- **Transition-gate receipts**: `87` compute / `88` memory at `e = 3`,
counted on the actual coordinate-expanded gate lists. -/
theorem b29_transition_gates :
    ((compTemplate F).transitionGates b).length = 87 ∧
      ((memTemplate F).transitionGates b).length = 88 ∧
      ((compTemplate F).transitionGates b).length = Nock.NockVM.comp_io_deg4_gates 3 ∧
      ((memTemplate F).transitionGates b).length = Nock.NockVM.mem_io_deg4_gates 3 :=
  ⟨(RAP_NockCompIO_transition_gates_e3 (K := K) b).1,
    (RAP_NockMemIO_transition_gates_e3 (K := K) b).1,
    (RAP_NockCompIO_transition_gates_e3 (K := K) b).2,
    (RAP_NockMemIO_transition_gates_e3 (K := K) b).2⟩

/-- **Headline receipts**: `395` total field elements per row and `175` total transition gates. -/
theorem b29_headline_totals :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).w
        + (RAP_NockMemIO b chalVal pubVal orbit Hm).w = 395 ∧
      ((compTemplate F).transitionGates b).length
        + ((memTemplate F).transitionGates b).length = 175 :=
  ⟨(constructed_total_columns_e3 b chalVal pubVal orbit Hc Hm).1,
    (constructed_total_transition_gates_e3 (K := K) b).1⟩

/-- **Degree receipt**: the declared `d = 4` is discharged, and every constraint polynomial of both
constructed RAPs really has total degree at most `4`. -/
theorem b29_degree_le_four :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).d = 4 ∧
      (∀ i, ((RAP_NockCompIO b chalVal pubVal orbit Hc).C i).totalDegree ≤ 4) ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).d = 4 ∧
      (∀ i, ((RAP_NockMemIO b chalVal pubVal orbit Hm).C i).totalDegree ≤ 4) :=
  ⟨(RAP_NockCompIO_maxDegree b chalVal pubVal orbit Hc).1,
    (RAP_NockCompIO_maxDegree b chalVal pubVal orbit Hc).2,
    (RAP_NockMemIO_maxDegree b chalVal pubVal orbit Hm).1,
    (RAP_NockMemIO_maxDegree b chalVal pubVal orbit Hm).2⟩

/-- **Round receipts**: two rounds for the compute chip, one for the memory chip, and both column splits sum to the declared width. -/
theorem b29_rounds :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).k = 2 ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).k = 1 ∧
      (RAP_NockCompIO b chalVal pubVal orbit Hc).w
        = ∑ r, (RAP_NockCompIO b chalVal pubVal orbit Hc).wRAP r ∧
      (RAP_NockMemIO b chalVal pubVal orbit Hm).w
        = ∑ r, (RAP_NockMemIO b chalVal pubVal orbit Hm).wRAP r :=
  ⟨rfl, rfl, (RAP_NockCompIO b chalVal pubVal orbit Hc).w_eq,
    (RAP_NockMemIO b chalVal pubVal orbit Hm).w_eq⟩

/-- **Endpoint receipts**: `2e` degree-`1` plus `e` degree-`3` gates and two equality checks for the
compute chip; `2e` degree-`1` plus `2e` degree-`3` gates and four equality checks for the memory
chip. -/
theorem b29_endpoints :
    ((compTemplate F).deg1Gates b).length = 6 ∧
      ((compTemplate F).deg3Gates b).length = 3 ∧
      ((compTemplate F).equalityGates).length = 2 ∧
      ((memTemplate F).deg1Gates b).length = 6 ∧
      ((memTemplate F).deg3Gates b).length = 6 ∧
      ((memTemplate F).equalityGates).length = 4 := by
  refine ⟨?_, ?_, RAP_NockCompIO_equality_checks (F := F), ?_, ?_,
    RAP_NockMemIO_equality_checks (F := F)⟩
  · rw [(RAP_NockCompIO_endpoint_gates (K := K) b).1]
  · rw [(RAP_NockCompIO_endpoint_gates (K := K) b).2.2.1]
  · rw [(RAP_NockMemIO_endpoint_gates (K := K) b).1]
  · rw [(RAP_NockMemIO_endpoint_gates (K := K) b).2.2.1]

/-! ## 3. Single field, single row domain -/

/-- **The constructed chip is one `Def:RAP`, not a segmented family.**  Its satisfaction is a single
quantification over one constraint index set `Fin s` and one row domain `H`. -/
theorem b29_single_rap_satisfaction
    (P : Fin (RAP_NockCompIO b chalVal pubVal orbit Hc).w → F[X]) :
    (RAP_NockCompIO b chalVal pubVal orbit Hc).Satisfies P
      ↔ ∀ i : Fin (RAP_NockCompIO b chalVal pubVal orbit Hc).s, ∀ x ∈ Hc,
          ((RAP_NockCompIO b chalVal pubVal orbit Hc).compose P i).eval x = 0 :=
  Iff.rfl

/-- **Both chips live over one base field and share the `Def:Canonical_RAP` common parameters**: same `ω`, `β`, `e`, `h`, and — when instantiated at the same domain — the same
row domain. -/
theorem b29_shared_domain_data (H : Finset F) :
    (RAP_NockCompIO b chalVal pubVal orbit H).ω = (RAP_NockMemIO b chalVal pubVal orbit H).ω ∧
      (RAP_NockCompIO b chalVal pubVal orbit H).β = (RAP_NockMemIO b chalVal pubVal orbit H).β ∧
      (RAP_NockCompIO b chalVal pubVal orbit H).e = (RAP_NockMemIO b chalVal pubVal orbit H).e ∧
      (RAP_NockCompIO b chalVal pubVal orbit H).h = (RAP_NockMemIO b chalVal pubVal orbit H).h ∧
      (RAP_NockCompIO b chalVal pubVal orbit H).H = (RAP_NockMemIO b chalVal pubVal orbit H).H :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Generic

/-! ## 4. -/

section Rows

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable {F₀ K₀ : Type} [Field F₀] [Field K₀] [Algebra F₀ K₀]

/-- **`N` rows for the compute chip**, over the BFS compute-row carrier. -/
theorem b29_compute_rows {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F)
    {cfg : ExactConfig F₀ K₀} (exec : ExactExecution cfg)
    (hH : H.card = exec.computeRows.length) :
    (RAP_NockCompIO b chalVal pubVal orbit H).H.card = cfg.compRows :=
  RAP_NockCompIO_rows b chalVal pubVal orbit H exec hH

/-- **`M + 2L` rows for the memory chip**, over the BFS memory-row carrier, under
the exact count-balance hypothesis equivalent to the budget. -/
theorem b29_memory_rows {e h : ℕ} (b : Basis (Fin e) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F e h) (H : Finset F)
    {cfg : ExactConfig F₀ K₀} {exec : ExactExecution cfg}
    (hbalance : RowLayout.RecordCountBalanced exec)
    (hH : H.card = exec.memoryRows.length) :
    (RAP_NockMemIO b chalVal pubVal orbit H).H.card
      = RowLayout.memoryM exec + 2 * RowLayout.memoryL exec :=
  RAP_NockMemIO_rows b chalVal pubVal orbit H hbalance hH

end Rows

/-! ## 5. The shape predicates have teeth -/

section Teeth

variable {F : Type*} [Field F]

/-- **The compute shape is not satisfied by the memory template**: `61 ≠ 62` extension columns, so
`CompIOShape` is a real discriminator and the compute fingerprints are not about every template. -/
theorem b29_memTemplate_is_not_compShape : ¬ CompIOShape (memTemplate F) := by
  intro hT
  have h1 : (memTemplate F).extCols = 61 := memTemplate_shape.ext_cols
  have h2 : (memTemplate F).extCols = 62 := hT.ext_cols
  omega

/-- **The memory shape is not satisfied by the compute template** either. -/
theorem b29_compTemplate_is_not_memShape : ¬ MemIOShape (compTemplate F) := by
  intro hT
  have h1 : (compTemplate F).extCols = 62 := compTemplate_shape.ext_cols
  have h2 : (compTemplate F).extCols = 61 := hT.ext_cols
  omega

/-- **A tampered width is rejected.**  A compute-shaped template cannot have a width other than
`62·e + 13`, so the width fingerprint is forced by the shape and not by the witness. -/
theorem b29_tampered_width_rejected {K : Type*} [Field K] [Algebra F K] [FiniteDimensional F K]
    {e h : ℕ} (T : ChipTemplate F) (hT : CompIOShape T) (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F)
    (hbad : (expandChip T b chalVal pubVal orbit H).w ≠ 62 * e + 13) : False :=
  hbad (compShape_width T b chalVal pubVal orbit H hT)

end Teeth

/-! ## 6. The old scoped `188/78` inequality is preserved -/

section OldGuard

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable [charRing : CharP K (ringChar K)]

/-- **Both facts hold at once.**  The OLD scoped segmented production object still has fingerprint
`(188, 78, 1)` and is still *not* the strict paper G10 package, while the NEW coordinate-expanded
monolithic pair *does* have the strict G10 fingerprint `(199, 196, 3)`.  Nothing was flipped: these
are two different objects. -/
theorem b29_old_inequality_and_new_equality
    (T : CompleteProductionCost.FinalProductionStrategy (F := F) (K := K))
    (ω : JointCoins K) (lmb : K)
    (hz : nprSeed ω ≠ 0)
    (rootBound gateBound ioBound : ℕ) :
    CompleteProductionCost.completeProductionAIRFingerprint
        (CompleteProductionCost.completeProductionCostAt
          T ω lmb hz rootBound gateBound ioBound) ≠
        CompleteProductionCost.strictPaperG10Fingerprint ∧
      (MonolithicRAP.concreteCompRAP.w, MonolithicRAP.concreteMemRAP.w,
          MonolithicRAP.concreteCompRAP.e)
        = CompleteProductionCost.strictPaperG10Fingerprint :=
  ⟨(Nock.RedTeam.b14_production_fingerprint_ne_strict_g10
      T ω lmb hz rootBound gateBound ioBound).2.2,
    MonolithicRAP.concrete_fingerprint_eq_strictG10⟩

end OldGuard

/-! ## 7. The residual, as a compiled artifact -/

section Residual

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- It says that the
`𝕂`-level gate list of a chip template *is* the chained strict table/walk/finite-field-IO language
`L` on `𝕂` environments.  Everything downstream of this hypothesis *is* proved — see
`b29_residual_closes_language`. -/
def B29SemanticTemplate (T : ChipTemplate F) (L : Env K → Prop) : Prop :=
  ∀ envK : Env K,
    L envK ↔ ∀ g ∈ T.extTransition ++ T.extDeg1 ++ T.extDeg3, g.eval envK = 0

/-- **Supplying the residual closes the satisfaction ⟺ language equivalence.**  Given a template
whose `𝕂`-level gates present the language `L`, the constructed monolithic RAP's `Def:RAP`
satisfaction is exactly: the base-field gates vanish pointwise, and `L` holds of the `𝕂`
environment gathered from the very same committed base columns.

The second, `hmix : T.mixedTransition = []`, is
**not** bookkeeping and this docstring claimed "No further hypothesis is needed" for one commit
while the signature already carried it.  The reason it is needed is structural: `L : Env K → Prop`
sees only the gathered `𝕂` environment, and `T.col0 e kind idx = T.baseCols + e·idx` is never
below `baseCols`, so `gatherEnv` provably discards exactly the base columns a mixed gate's
`Lift`/`Scale` leaves read.  **A one-argument `Env K` language therefore cannot express a mixed
gate at all** — the two-environment form `MonolithicRAP.expandChip_satisfies_iff_language` uses is
the only one that can.  Both call sites (`StrictPackage.comp_satisfies_iff_language` /
`mem_satisfies_iff_language`) discharge `hmix` by `rfl`, because the monolithic `compTemplate` /
`memTemplate` keep an empty mixed bucket; the optimized memory chip, which does not, is served by
`OptimizedMemoryCanonicalSatisfaction.sourceMemoryRAP_satisfies_iff_language` instead. -/
theorem b29_residual_closes_language {e h : ℕ} (T : ChipTemplate F) (L : Env K → Prop)
    (hsem : B29SemanticTemplate (K := K) T L) (hmix : T.mixedTransition = [])
    (b : Basis (Fin e) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictOrbitDomain F e h) (H : Finset F)
    (P : Fin (expandChip T b chalVal pubVal orbit H).w → F[X]) :
    (expandChip T b chalVal pubVal orbit H).Satisfies P
      ↔ ∀ x ∈ H,
          (∀ g ∈ T.baseTransition,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ (∀ g ∈ T.equalityChecks,
              g.eval (Reify.envOfTrace P orbit.ω x chalVal pubVal) = 0)
            ∧ L (gatherEnv b (T.col0 e) (Reify.envOfTrace P orbit.ω x chalVal pubVal)) := by
  rw [expandChip_satisfies_iff_language T b chalVal pubVal orbit H P]
  refine forall_congr' fun x => ?_
  refine imp_congr_right fun _ => ?_
  rw [hsem (gatherEnv b (T.col0 e) (Reify.envOfTrace P orbit.ω x chalVal pubVal))]
  simp only [hmix, List.not_mem_nil, false_implies, implies_true, and_true]

/-- **The residual predicate is inhabited in general** (it is not an impossible obligation): every
template presents *some* language, namely the vanishing of its own `𝕂`-level gates. -/
theorem b29_residual_satisfiable (T : ChipTemplate F) :
    B29SemanticTemplate (K := K) T
      (fun envK => ∀ g ∈ T.extTransition ++ T.extDeg1 ++ T.extDeg3, g.eval envK = 0) :=
  fun _ => Iff.rfl

end Residual

end

end Nock.RedTeam.Batch29

#print axioms Nock.RedTeam.Batch29.b29_constructed_pair_nonvacuous
#print axioms Nock.RedTeam.Batch29.b29_concrete_fingerprint
#print axioms Nock.RedTeam.Batch29.b29_concrete_omega_order
#print axioms Nock.RedTeam.Batch29.b29_widths
#print axioms Nock.RedTeam.Batch29.b29_transition_gates
#print axioms Nock.RedTeam.Batch29.b29_headline_totals
#print axioms Nock.RedTeam.Batch29.b29_degree_le_four
#print axioms Nock.RedTeam.Batch29.b29_rounds
#print axioms Nock.RedTeam.Batch29.b29_endpoints
#print axioms Nock.RedTeam.Batch29.b29_single_rap_satisfaction
#print axioms Nock.RedTeam.Batch29.b29_shared_domain_data
#print axioms Nock.RedTeam.Batch29.b29_compute_rows
#print axioms Nock.RedTeam.Batch29.b29_memory_rows
#print axioms Nock.RedTeam.Batch29.b29_memTemplate_is_not_compShape
#print axioms Nock.RedTeam.Batch29.b29_compTemplate_is_not_memShape
#print axioms Nock.RedTeam.Batch29.b29_tampered_width_rejected
#print axioms Nock.RedTeam.Batch29.b29_old_inequality_and_new_equality
#print axioms Nock.RedTeam.Batch29.b29_residual_closes_language
#print axioms Nock.RedTeam.Batch29.b29_residual_satisfiable
