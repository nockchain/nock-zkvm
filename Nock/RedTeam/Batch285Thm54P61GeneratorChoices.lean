/-
  Nock/RedTeam/Batch285Thm54P61GeneratorChoices.lean

  `Batch263.b263_nockCompiles_grom` inhabits `nockCompiles_of_grom_atTree` at
  `DotConfig769` by passing `b216Chal`, `dot_hinp`, `memoryInputs_eq`,
  `stateTagChar`, and the five trailing coins.

  The claim conjunct is `package.optimized.verifier.raw.claim = ⟨dotSubject,
  dotFormula, dotResult⟩`, the in-tree form of `claimedResult = result`.

  **Not claimed.**
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.RedTeam.Batch221Thm54BuildableAtTierA
import Nock.RedTeam.Batch263Thm54BoundedPremisesAtTierA
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch285

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section

/-- The compiler challenge vector at Tier A's coins is the vector `Batch216` already
used. -/
theorem b285_chal_eq_b216 :
    compilerChallengeVector (K := DK) alphaA seedZ 0 0 0 MemoryTable.formRDefault = Batch216.b216Chal :=
  rfl

/-- `hKsz2` at the compiler vector, transported from `Batch191` off `b285_chal_eq_b216`. -/
theorem b285_hKsz2 :
    2 * (genExactConfig (F := DF) (compilerChallengeVector alphaA seedZ 0 0 0 MemoryTable.formRDefault)
      64 executionOrbit Batch216.b216_horb
      (genComputeRows seedZ alphaA (dotTree (K := DK)))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le).kMem ≤ 64 := by
  rw [b285_chal_eq_b216]
  exact Batch191.b191_hKsz2

/-- The program-level `hrows` at Tier A (both row counts `≤ 2^8`, `3·256 < 769`). -/
theorem b285_dot_hrows :
    3 * (bfsRows (airReorder (dotTree (K := DK)))).length < ringChar DK ∧
      programMemShape alphaA (dotTree (K := DK)) < ringChar DK := by
  have h1 := Batch216.b216_comp_le
  rw [genComputeRows_bfsForest_length] at h1
  have h2 : programMemShape alphaA (dotTree (K := DK)) ≤ 2 ^ executionOrbit.h := by
    rw [programMemShape_spec (lmb := MemoryTable.formRDefault) seedZ]
    exact Batch216.b216_mem_le
  norm_num [DotConfig769.executionOrbit] at h1 h2
  rw [DotConfig769.ringChar_K]
  constructor <;> omega

/-- The memory half of §1's `hwin` (weakest form) at Tier A:
`184` memory rows, `orderOf α = 192`. -/
theorem b285_dot_hmemOrd :
    programMemShape alphaA (dotTree (K := DK)) ≤ orderOf alphaA := by
  rw [programMemShape_spec (lmb := MemoryTable.formRDefault) seedZ]
  change (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
    (dotTree (K := DK)))).length ≤ orderOf alphaA
  rw [Batch180.dot_memRowsLen, Batch180.alphaA_order_eq_192]
  norm_num

/-- **`nockCompiles_of_grom_atTree_p61` at Tier A.** -/
noncomputable def b285_nockCompiles_p61 :=
    (nockCompiles_of_grom_atTree_p61 (F := DF) (q := 769) (Λ := DotConfig769.Λ)
      seedZ alphaA alphaA MemoryTable.formRDefault seedZ_ne_zero two_ne_zero 0 0 0
      64 DotConfig769.executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
      Batch263.b263_subject_bounded Batch263.b263_formula_bounded Batch263.b263_grom
      (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
      (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
      192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
      (by have := Batch180.dot_accAt_le; omega)
      (by rw [Batch180.dot_memRowsLen, Batch180.alphaA_order_eq_192]; norm_num)
      (by have := Batch180.dot_accAt_le; omega)
      b285_hKsz2
      (by norm_num) DotConfig769.ringChar_K.symm
      Batch180.dot_hlt
      (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
      Batch180.dot_gen_hout
      Batch221.b221_hKszChar Batch221.b221_hprogCap Batch221.b221_hmemCap
      DotConfig769.basis DotConfig769.strictOrbit Batch251.b251_hcap
      255 Batch251.b251_hreqn Batch251.b251_hrespn Batch246.b246_hcard
      b285_dot_hrows DotConfig769.dot_primeField
      Batch221.b221_laterSeedZeros)

end

end Nock.RedTeam.Batch285

#print axioms Nock.RedTeam.Batch285.b285_chal_eq_b216
#print axioms Nock.RedTeam.Batch285.b285_hKsz2
#print axioms Nock.RedTeam.Batch285.b285_nockCompiles_p61
