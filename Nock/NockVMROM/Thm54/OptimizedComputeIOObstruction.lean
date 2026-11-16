import Nock.NockVMROM.Thm54.OptimizedComputeOverlay
import Nock.NockVMROM.Thm54.PlusIOTraceEncoding
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Exact program-IO field obstruction for the monolithic compute chip

The author-approved six-slot overlay is a `K`-valued row.  The exact program-IO obligation that
the requested capstone must target, however, is not `K`-valued:

`PlusIOSameExecutionAssignment.exactIO.progAcc : ℕ → IOField K`, where
`IOField K = RatFunc (RatFunc K)`.

This is not a representational inconvenience that another state-dependent sharing map can solve.
The outer rational-function field is transcendental over its coefficient field and therefore has
no finite basis, in particular no degree-three basis.  When `K` is finite (the paper's
Goldilocks/cubic setting), there is not even an injective scalar codec from `IOField K` to `K`.

The repository's `FiniteFieldIO` packet is a different, sampled finite-field replacement.  Its
own specification explicitly excludes counted collision events; it is not an exact all-challenge
biconditional to `IO.ProgIOSat`.  Consequently the simultaneous requirements

* degree-three `ChipTemplate F` extension columns in `K`,
* exact all-trace equivalence to the existing `PlusIOSameExecutionAssignment` compute projection,
* and no additional correctness delta replacing symbolic IO

are mathematically incompatible.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeIOObstruction

open Nock
open Module

/-- The exact assignment's program accumulator has the nested rational-function type. -/
theorem exact_program_accumulator_type
    {F K : Type} [Field F] [Field K] [Algebra F K]
    {p : ℕ} [CharP K p] {R : PlusIOSegmentedFamily F K}
    (A : PlusIOSameExecutionAssignment R p) :
    (A.exactIO.progAcc : ℕ → IOField K) = A.exactIO.progAcc :=
  rfl

/-- A rational-function field cannot have a three-element basis over its coefficient field. -/
theorem no_degree_three_basis_ratFunc (L : Type*) [Field L] :
    ¬ Nonempty (Basis (Fin 3) L (RatFunc L)) := by
  rintro ⟨b⟩
  letI : FiniteDimensional L (RatFunc L) := b.finiteDimensional_of_finite
  exact (Algebra.transcendental_iff_not_isAlgebraic.mp RatFunc.transcendental)
    (Algebra.IsAlgebraic.of_finite L (RatFunc L))

/-- In particular, the outer field used by exact program IO has no degree-three basis over its
coefficient field `RatFunc K`. -/
theorem no_degree_three_basis_IOField_over_coeff (K : Type*) [Field K] :
    ¬ Nonempty (Basis (Fin 3) (RatFunc K) (IOField K)) :=
  no_degree_three_basis_ratFunc (RatFunc K)

/-- Over a finite extension field there is no lossless scalar codec for exact symbolic IO values. -/
theorem no_injective_IOField_to_finite (K : Type*) [Field K] [Finite K] :
    ¬ ∃ encode : IOField K → K, Function.Injective encode := by
  rintro ⟨encode, hencode⟩
  letI : Algebra.Transcendental (RatFunc K) (IOField K) := RatFunc.transcendental
  letI : Infinite (IOField K) := Algebra.Transcendental.infinite (RatFunc K) (IOField K)
  letI : Finite (IOField K) := Finite.of_injective encode hencode
  exact not_finite (IOField K)

/-- Hence no encode/decode pair can round-trip every exact program-IO accumulator scalar through
one `K`-valued extension slot. -/
theorem no_scalar_roundtrip_IOField_to_finite (K : Type*) [Field K] [Finite K] :
    ¬ ∃ (encode : IOField K → K) (decode : K → IOField K),
        Function.LeftInverse decode encode := by
  rintro ⟨encode, decode, hround⟩
  exact no_injective_IOField_to_finite K ⟨encode, hround.injective⟩

#print axioms exact_program_accumulator_type
#print axioms no_degree_three_basis_ratFunc
#print axioms no_degree_three_basis_IOField_over_coeff
#print axioms no_injective_IOField_to_finite
#print axioms no_scalar_roundtrip_IOField_to_finite

end OptimizedComputeIOObstruction
end Nock.NockVMROM.Thm54
