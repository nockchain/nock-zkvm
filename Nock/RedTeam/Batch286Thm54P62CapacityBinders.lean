/-
  Nock/RedTeam/Batch286Thm54P62CapacityBinders.lean

  `Batch285.b285_nockCompiles_p61` still passed `Ksz = 64`, `B = 192`,
  `n = 255` and the five comparisons they fed.

  The claim conjunct is `package.optimized.verifier.raw.claim = ⟨dotSubject,
  dotFormula, dotResult⟩`, the in-tree form of `claimedResult = result`.

  **Not claimed.**
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesBounded
import Nock.RedTeam.Batch285Thm54P61GeneratorChoices
import Nock.RedTeam.Batch246Thm54InputsAtGeneratedCarrier
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch286

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




/-- The compiler IO window at Tier A is `max 13 20 = 20`. -/
theorem b286_compilerKsz :
    compilerKszOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) = 20 := by
  have hacc : programAcc (dotTree (K := DK)) = 13 := Batch211.b211_accAt_eq_13
  have hmf : programMemRootsL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) = 10 := by
    unfold programMemRootsL
    rw [Batch180.dot_genMemoryForest]
    exact threaded_kMem _ _
  rw [compilerKszOfL, compilerKsz, hacc, hmf]; norm_num

/-- The compiler record bound at Tier A is `max 13 184 = 184`. -/
theorem b286_compilerN :
    compilerNOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) = 184 := by
  have hacc : programAcc (dotTree (K := DK)) = 13 := Batch211.b211_accAt_eq_13
  have hmem : programMemRowsL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) = 184 :=
    Batch180.dot_memRowsLen
  rw [compilerNOfL, compilerN, hacc, hmem]; norm_num

/-- `hwin` at the chosen `B = orderOf α`. -/
theorem b286_hwin :
    programAcc (dotTree (K := DK)) + 3 < orderOf alphaA := by
  rw [programAcc, Batch211.b211_accAt_eq_13, Batch180.alphaA_order_eq_192]
  norm_num

/-- `hKszChar` at the chosen `Ksz`. -/
theorem b286_hKszChar :
    compilerKszOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)) < ringChar DK := by
  rw [b286_compilerKsz, DotConfig769.ringChar_K]
  norm_num

/-- `hcard` at the chosen `n`, by monotonicity from the capacity ceiling `255`. -/
theorem b286_hcard :
    RecordCarrier.honestIOBound
      (compilerNOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)))
      (compilerNOfL (K := DK) MemoryTable.formRDefault seedZ alphaA (dotTree (K := DK)))
      (Fintype.card DK) < Fintype.card (DK × DK) := by
  rw [b286_compilerN]
  exact lt_of_le_of_lt
    (RecordCarrier.honestIOBound_mono _
      (by norm_num : (184 : ℕ) ≤ 255) (by norm_num : (184 : ℕ) ≤ 255))
    Batch246.b246_hcard

/-- **`nockCompiles_of_grom_atTree_p62` at Tier A.**  Same program as
`Batch285.b285_nockCompiles_p61`; the caller no longer supplies `Ksz`, `B`,
`n`, `hB`, `hKsz`, `hKsz2`, `hreqn` or `hrespn`. -/
noncomputable def b286_nockCompiles_p62 :=
  nockCompiles_of_grom_atTree_p62 (F := DF) (q := 769) (Λ := DotConfig769.Λ)
    seedZ alphaA alphaA MemoryTable.formRDefault seedZ_ne_zero two_ne_zero 0 0 0
    DotConfig769.executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    Batch263.b263_subject_bounded Batch263.b263_formula_bounded Batch263.b263_grom
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_comp_le Batch216.b216_mem_le
    b286_hwin Batch285.b285_dot_hmemOrd
    (by norm_num) DotConfig769.ringChar_K.symm
    Batch180.dot_hlt
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout
    b286_hKszChar Batch221.b221_hprogCap Batch221.b221_hmemCap
    DotConfig769.basis DotConfig769.strictOrbit Batch251.b251_hcap
    b286_hcard
    Batch285.b285_dot_hrows DotConfig769.dot_primeField Batch221.b221_laterSeedZeros

end

end Nock.RedTeam.Batch286

#print axioms Nock.RedTeam.Batch286.b286_compilerKsz
#print axioms Nock.RedTeam.Batch286.b286_compilerN
#print axioms Nock.RedTeam.Batch286.b286_hwin
#print axioms Nock.RedTeam.Batch286.b286_hKszChar
#print axioms Nock.RedTeam.Batch286.b286_hcard
#print axioms Nock.RedTeam.Batch286.b286_nockCompiles_p62
