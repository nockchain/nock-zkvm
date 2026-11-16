import Nock.NockVMROM.Thm54.OptimizedComputeCodec
import Nock.NockVMROM.Thm54.ConcreteStrictPackage

/-!
# Concrete non-vacuity for the normalized compute codec

This is implementation evidence only.  It instantiates the normalized codec with the honest
cubic OP1 compute row from `ConcreteStrictPackage`; it is not a padded-RAP witness and does not
close R6.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedComputeCodecConcrete

open Nock.ComputeTable
open ConcreteStrictPackage
open OptimizedComputeCodec

/-- The inverse columns are irrelevant to `Vcomp`, so zero is a valid codec witness for this
roundtrip receipt.  The future optimized gate basis must constrain them where their gates are
active. -/
noncomputable def honestExtra : Extra K73cubic := ⟨0, 0⟩

/-- A concrete normalized 13/58 row over the production cubic carrier. -/
noncomputable def honestRow : Row F73 K73cubic :=
  encode (computePub honestSeed honestAlpha) (computeDec honestSeed) honestExtra

theorem honestRow_decode :
    decode (computeInputs honestSeed honestAlpha) honestRow =
      ({ computePub honestSeed honestAlpha with
          sf1_st := none, sf2_st := none, sf3_st := none, certC? := none },
        computeDec honestSeed, honestExtra) := by
  exact decode_encode_of_vcomp compute_accepts

theorem normalized_row_nonempty : Nonempty (Row F73 K73cubic) :=
  ⟨honestRow⟩

#print axioms honestRow_decode
#print axioms normalized_row_nonempty

end OptimizedComputeCodecConcrete
end Nock.NockVMROM.Thm54
