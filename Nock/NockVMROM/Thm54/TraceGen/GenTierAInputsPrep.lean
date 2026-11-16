/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAInputsPrep.lean

  Backend field data for a future `Inputs` over `DotConfig769`: state-tag
  characteristic, `𝔽_769`-basis of the cubic, cardinality `|K| = 769^3`,
  and the IO failure-union bound against `|K|²` using the length caps
  `≤ 24` requests / `≤ 184` responses.  Does not construct `Inputs E`
  (needs `BuildableNockExecution`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierABuildableParts769
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Nock.NockVMROM.Thm54.GenericHonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.CoordinateBasis
open FiniteIO

noncomputable instance : Fintype K := Fintype.ofFinite K

noncomputable instance : DecidableEq K := Classical.decEq K

instance : FiniteDimensional F K := inferInstance

theorem stateTagChar : NodeEncoding.StateTagChar K :=
  NodeEncoding.stateTagChar_of_charP (K := K) 769 (by norm_num)

theorem card_K : Fintype.card K = 769 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 769 3 (by norm_num)

noncomputable def basis : Module.Basis (Fin 3) F K :=
  stdCoordBasis F K 3 finrank_cubic

theorem ioFailureUnionBound_lt_card_prod :
    ioFailureUnionBound 8 24 184 (Fintype.card K) < Fintype.card (K × K) := by
  rw [ioFailureUnionBound, Fintype.card_prod, card_K]
  norm_num

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.stateTagChar
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.card_K
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.basis
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.strictOrbit
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.ioFailureUnionBound_lt_card_prod
