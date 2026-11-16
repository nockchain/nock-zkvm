/-
  Nock/RedTeam/Batch232Thm54BroadProgramData.lean

  **The rest of the chain at the broad program: `mt`, `BuildableNockExecution`, `Data`.**

  `Batch231` supplied every hypothesis of `genSemanticData` at the seventeen-row, eight-state
  program.  The three objects downstream of it — `genServedMemoryTrace` (`FZ`, `GA`),
  `genBuildableOfProgram` (`GB`) and `genData` (`GG`) — each add a handful of numeric side
  conditions and nothing else, so they follow at the same configuration.

  `GG`'s "Not claimed" list opens with **"`genData` is not instantiated"** and says joint
  satisfiability of its premise list is open in the sense `GA` §1 warns about.  This module closes
  that, at a program with eight of the eleven states rather than four.  The four extra numbers are

  | side condition | value here |
  |---|---|
  | `hKsz2 : 2 * kMem ≤ Ksz` | `2 * 19 = 38 ≤ 64` |
  | `hKszChar : Ksz < ringChar K` | `64 < 769` |
  | `hprogCap : accAt + 1 ≤ 2 ^ h` | `≤ 52 ≤ 256` |
  | `hmemCap : memRows + 1 ≤ 2 ^ h` | `228 ≤ 256` |

  and `GB` §3's observation that `hKszChar` and `hKsz`/`hKsz2` pull `Ksz` in opposite directions is
  met the same way it was at Tier A: `max 51 38 ≤ 64 < 769`.

  **Not claimed.**
-/
import Nock.RedTeam.Batch231Thm54BroadProgramSemanticData
import Nock.NockVMROM.Thm54.TraceGen.GenServedMemoryTrace
import Nock.NockVMROM.Thm54.TraceGen.GenBuildableAssembly
import Nock.NockVMROM.Thm54.TraceGen.GenHonestData

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch232

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

abbrev DK := Batch231.DK
abbrev DF := Batch231.DF

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

/-! ## The four numeric side conditions -/

theorem bp_kMem :
    (genExactConfig (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
      (by norm_num [DotConfig769.executionOrbit])
      (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
      Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem).kMem = 19 := by
  rw [genExactConfig_kMem]
  exact bp_memoryForest_length _ _ _

theorem bp_hKsz2 :
    2 * (genExactConfig (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
      (by norm_num [DotConfig769.executionOrbit])
      (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
      Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem).kMem ≤ 64 := by
  rw [bp_kMem]; norm_num

theorem bp_hKszChar : (64 : ℕ) < ringChar DK := by
  have h : ringChar DK = 769 := DotConfig769.ringChar_K
  rw [h]; norm_num

theorem bp_hprogCap :
    accAt (airReorder (bpTree (K := DK)))
      (bfsRows (airReorder (bpTree (K := DK)))).length + 1
      ≤ 2 ^ DotConfig769.executionOrbit.h := by
  have h := Batch231.bp_accAt_le
  have h2 : (2 : ℕ) ^ DotConfig769.executionOrbit.h = 256 := by
    norm_num [DotConfig769.executionOrbit]
  omega

theorem bp_hmemCap :
    (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
      (memInputs DotConfig769.seedZ) (bpTree (K := DK)))).length + 1
      ≤ 2 ^ DotConfig769.executionOrbit.h := by
  rw [bp_memRowsLen]
  norm_num [DotConfig769.executionOrbit]

/-! ## `mt` at the broad program -/

/-- **`ExactServedMemoryTrace` at the broad program**, from `genServedMemoryTrace`.  The second
program at which the served-forest trace has ever been inhabited (`GA` closed the first). -/
noncomputable def bp_mt
     :=
  genServedMemoryTrace (F := DF) (q := 769) (Λ := 22)
    DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 1
    Batch231.bpChal Batch231.bp_hinp Batch231.bp_hmi
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_bp 0)
    Batch231.bp_seedGood_at769
    (bp_computeCoins _ _)
    (by norm_num) Batch231.bp_air_traceConfined
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch231.bp_accAt_le; omega)
    (by have := Batch231.bp_accAt_le; omega)
    bp_hKsz2
    Batch231.bp_hb (by norm_num) DotConfig769.ringChar_K.symm Batch231.bp_haxis
    (not_mem_badSeeds_of_pairs _ _
      (bp_pairs_sep DotConfig769.seedZ Batch231.bp_ringChar_gt_two
        (Batch231.bp_sepSeed_one_two _) _))
    Batch231.bp_hout Batch231.bp_hlt

/-! ## `BuildableNockExecution` at the broad program -/

/-- **A `BuildableNockExecution DF DK` at the broad program**, from `genBuildableOfProgram`.
`GB`'s assembly, at its second configuration. -/
noncomputable def bp_buildable
     :
    BuildableNockExecution DF DK :=
  genBuildableOfProgram (F := DF) (q := 769) (Λ := 22)
    DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 1
    Batch231.bpChal Batch231.bp_hinp Batch231.bp_hmi
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_bp 0)
    Batch231.bp_seedGood_at769
    (bp_computeCoins _ _)
    (by norm_num) Batch231.bp_air_traceConfined
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch231.bp_accAt_le; omega)
    (by have := Batch231.bp_accAt_le; omega)
    bp_hKsz2
    Batch231.bp_hb (by norm_num) DotConfig769.ringChar_K.symm Batch231.bp_haxis
    (not_mem_badSeeds_of_pairs _ _
      (bp_pairs_sep DotConfig769.seedZ Batch231.bp_ringChar_gt_two
        (Batch231.bp_sepSeed_one_two _) _))
    Batch231.bp_hout
    bp_hKszChar bp_hprogCap bp_hmemCap Batch231.bp_hlt

theorem bp_laterSeedZeros : BuildableAxisWitness.LaterSeedZeros bp_buildable :=
  genBuildableOfProgram_laterSeedZeros

/-! ## `Data` at the broad program

`GG`'s "Not claimed" list opens with "`genData` is not instantiated"; this is the term. -/

/-- **`HonestCommitment.Data` at the broad program** — the honest prover's seed-free commitment at a program with eight of the eleven compute states.  Its sixteen fields are
`genData`'s, and its carrier is `genBuildable` at exactly the arguments `bp_buildable` uses. -/
noncomputable def bp_data
     :=
  genData (F := DF) DotConfig769.seedZ DotConfig769.alphaA 0 0 1
    Batch231.bpChal Batch231.bp_hinp
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_bp 0)
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
    769 (by norm_num) 22 (by norm_num)
    Batch231.bp_air_traceConfined
    Batch231.bp_hb (by norm_num) DotConfig769.ringChar_K.symm Batch231.bp_haxis
    Batch231.bp_semanticData
    bp_mt
    (genExactExecution_requestNodup (F := DF) DotConfig769.seedZ DotConfig769.alphaA
      Batch231.bpChal 64 DotConfig769.executionOrbit
      (by norm_num [DotConfig769.executionOrbit]) 0 0 1 (bpTree (K := DK))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
      Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
      (horb_of_window (le_of_eq Batch180.alphaA_order_eq_192.symm)
        (by have := Batch231.bp_accAt_le; omega)))
    (genBuildable_hbal (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
      (by norm_num [DotConfig769.executionOrbit])
      DotConfig769.seedZ DotConfig769.alphaA 0 0 1 (memInputs DotConfig769.seedZ)
      (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
      (bpTree (K := DK)) Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem)
    (le_of_eq DotConfig769.ringChar_K.symm) DotConfig769.two_ne_zero bp_hKszChar
    (genBuildable_hprog (F := DF) DotConfig769.seedZ DotConfig769.alphaA
      Batch231.bpChal 64 DotConfig769.executionOrbit
      (by norm_num [DotConfig769.executionOrbit]) 0 0 1 (bpTree (K := DK))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
      Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem bp_hprogCap)
    (genBuildable_hresp (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
      (by norm_num [DotConfig769.executionOrbit]) 0 0 1
      (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
      Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem bp_hmemCap)

/-! ## Measured off the assembled objects -/

theorem bp_buildable_q
     :
    bp_buildable.q = 769 := rfl

theorem bp_buildable_Λ
     :
    bp_buildable.Λ = 22 := rfl

theorem bp_data_Λ
     :
    bp_data.Λ = 22 := rfl

theorem bp_data_nounSizeBound
     :
    bp_data.nounSizeBound = 22 := rfl

end Nock.RedTeam.Batch232

#print axioms Nock.RedTeam.Batch232.bp_kMem
#print axioms Nock.RedTeam.Batch232.bp_hKsz2
#print axioms Nock.RedTeam.Batch232.bp_mt
#print axioms Nock.RedTeam.Batch232.bp_buildable
#print axioms Nock.RedTeam.Batch232.bp_data
#print axioms Nock.RedTeam.Batch232.bp_buildable_q
#print axioms Nock.RedTeam.Batch232.bp_data_Λ
