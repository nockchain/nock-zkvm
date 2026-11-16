import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.CoordinateRAPTail
import Nock.Framework.FixedPreprocessingRAP

/-!
# Named source and final optimized memory RAPs

The final object
applies only the author-authorized post-semantic residual padding, from `182/156` to `205/156`.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryRAP

open Nock
open Nock.Framework
open Module
open scoped Polynomial
open MonolithicRAP
open StrictExtension
open OptimizedMemoryGateBasis
open OptimizedMemoryCanonicalTrace

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K]

def sourceMemoryRAP {h : ℕ}
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  expandChipTail (memorySourceTemplate b) b chalVal pubVal orbit H 2

theorem sourceMemoryRAP_fingerprint {h : ℕ}
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (sourceMemoryRAP b chalVal pubVal orbit H).w = 182 ∧
      (sourceMemoryRAP b chalVal pubVal orbit H).s = 156 ∧
      (sourceMemoryRAP b chalVal pubVal orbit H).d = 4 ∧
      (sourceMemoryRAP b chalVal pubVal orbit H).k = 1 := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  change ((memorySourceTemplate b).allGates b).length = 156
  rw [ChipTemplate.length_allGates]
  rw [ChipTemplate.length_transitionGates, ChipTemplate.length_deg1Gates,
    ChipTemplate.length_deg3Gates, ChipTemplate.length_equalityGates]
  simp only [memorySourceTemplate_shape b, memorySourceTemplate_mixed_shape b]

def namedSourceMemoryRAP {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) : FixedPreprocessingRAP F where
  rap := sourceMemoryRAP b chalVal pubVal orbit (rowNodeSet nodes)
  rounds_pos := by
    rw [(sourceMemoryRAP_fingerprint b chalVal pubVal orbit (rowNodeSet nodes)).2.2.2]
    omega
  fixedCount := 4
  preprocessingIndex :=
    { toFun := fun j =>
        if h3 : (j : ℕ) = 3 then ⟨154, by change 154 < 182; omega⟩
        else if h2 : (j : ℕ) = 2 then ⟨153, by change 153 < 182; omega⟩
        else ⟨4 + (j : ℕ), by
          change 4 + (j : ℕ) < 182
          have hj : (j : ℕ) < 4 := j.isLt
          omega⟩
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first | rfl | cases hij }
  preprocessing
    | 0 => OptimizedMemoryCanonicalTrace.firstRowMask nodes
    | 1 => OptimizedMemoryCanonicalTrace.lastRowMask nodes
    | 2 => OptimizedMemoryCanonicalTrace.rootRowMask nodes kMem
    | 3 => OptimizedMemoryCanonicalTrace.dequeueRowMask nodes kMem

theorem canonicalSourceTrace_binds
    [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]
    {R : PlusIOSegmentedFamily F K}
    {h : ℕ} (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit kMem).BindsPreprocessing
      (canonicalSourceTrace A nodes b kMem) := by
  intro j
  fin_cases j
  · change (canonicalSourceTrace A nodes b kMem) 4 =
      OptimizedMemoryCanonicalTrace.firstRowMask nodes
    exact canonicalSourceTrace_first_fixed A nodes b kMem
  · change (canonicalSourceTrace A nodes b kMem) 5 =
      OptimizedMemoryCanonicalTrace.lastRowMask nodes
    exact canonicalSourceTrace_last_fixed A nodes b kMem
  · change (canonicalSourceTrace A nodes b kMem) ⟨153, by omega⟩ =
      OptimizedMemoryCanonicalTrace.rootRowMask nodes kMem
    exact canonicalSourceTrace_root_fixed A nodes b kMem
  · change (canonicalSourceTrace A nodes b kMem) ⟨154, by omega⟩ =
      OptimizedMemoryCanonicalTrace.dequeueRowMask nodes kMem
    exact canonicalSourceTrace_dequeue_fixed A nodes b kMem

/-- Final `196/113`, degree-four, one-round memory RAP.  The residual gates/columns are introduced
only after the semantic source object exists and has an exact satisfaction language.

**Stage 3b.**  The residual gate count is `RAPPadding.memoryResidualTransitionGates`,
not the compute-shared `RAPPadding.residualTransitionGates` (eleven): after the four memory scalar
gates were retyped as `𝕂`-valued mixed gates the source chip's transition bucket carried `24·e`
rather than `21·e + 3`, so only five inert slots were needed to reach the paper's `24·e + 16`.
The column padding is unchanged, so `w` is still
`196`. -/
def namedFinalMemoryRAP {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) : FixedPreprocessingRAP F :=
  let S := namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem
  RAPPadding.padFixedPreprocessing S
    (RAPPadding.firstRoundExtra S.rap S.rounds_pos
      (RAPPadding.memoryResidualColumns 3))
    (RAPPadding.memoryResidualTransitionGates 3)

theorem finalMemoryRAP_fingerprint {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.w = 205 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.s = 156 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.d = 4 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.k = 1 := by
  let S := namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem
  have hsource := sourceMemoryRAP_fingerprint b chalVal pubVal orbit (rowNodeSet nodes)
  have hpad := RAPPadding.padMemoryCoreMixed_e3_carrier_fingerprint S.rap S.rounds_pos
    hsource.1 hsource.2.1
  exact ⟨hpad.1, hpad.2, hsource.2.2.1, hsource.2.2.2⟩

/-- The memory chip's recorded `Def:RAP` extension degree, i.e. the `e` of the
tuple `(𝕂, e)`.  `RAPPadding.pad_e` carries it through the residual padding unchanged, so the
final chip records the degree of the basis it was expanded over.  This is the quantity
Theorem 5.4's memory resource list is affine in. -/
theorem finalMemoryRAP_e {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.e = 3 := rfl

theorem final_satisfies_iff_source {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ)
    (P : Fin (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing
        (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem) P ↔
      RAP.SatisfiesWithPreprocessing
        (namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem)
        (RAPPadding.projectTrace
          (namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap
          (RAPPadding.firstRoundExtra
            (namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap
            (namedSourceMemoryRAP hn nodes b chalVal pubVal orbit kMem).rounds_pos
            (RAPPadding.memoryResidualColumns 3)) P) := by
  exact RAPPadding.padFixedPreprocessing_satisfies_iff _ _ _ P

end
end OptimizedMemoryRAP
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryRAP.sourceMemoryRAP_fingerprint
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryRAP.canonicalSourceTrace_binds
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryRAP.finalMemoryRAP_fingerprint
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryRAP.finalMemoryRAP_e
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryRAP.final_satisfies_iff_source
