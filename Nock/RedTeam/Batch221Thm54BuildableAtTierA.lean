/-
  Nock/RedTeam/Batch221Thm54BuildableAtTierA.lean

  **`BuildableNockExecution` inhabited at the generated carrier.**

  This
  module applies the same test one level up.  `b221Buildable` is a **term** of
  `BuildableNockExecution DF DK` built by `genBuildableOfProgram`, so `genBuildable`'s whole
  fourteen-argument list — `sd`, `mt`, `hnodup`, `hbal` and the five arithmetic side conditions —
  is jointly satisfiable at a real program.

  **The three premises `genBuildableOfProgram` carries, discharged here.**  `hKszChar` and
  `genSemanticData`'s `hKsz` pull `Ksz` in opposite directions, so their joint satisfiability was
  the open question: `Ksz = 64` satisfies `accAt = 13 ≤ 64`, `2 · kMem = 20 ≤ 64` and
  `64 < 769 = ringChar DK` simultaneously.  `hprogCap` is `13 + 1 ≤ 256` and `hmemCap` is
  `184 + 1 ≤ 256`, at `orbit.h = 8`.

  **Non-vacuity is measured on the assembled object.**  `b221_requestIO_length` reads `13` off
  `b221Buildable.exec` (not off a lemma about a list that might be a different list),
  `b221_requestIO_ts` identifies the timestamp column as `alphaA^1 … alphaA^13`, and
  `b221_requestNodup` is the structure's own `requestNodup` field on that thirteen-entry list.
  So the `Nodup` is neither `Nodup []` nor `Nodup [x]`.

  **Scope.**  One configuration, one program — Tier A over `GaloisField 769 3`, seed `φ(8)`,
  `α = φ(4)`, coins `(0,0,0)`, `Ksz = 64`, `Λ = 22`.  Nothing here is a capstone:
  `HonestCommitment.Data`'s sixteen fields, `Inputs`, `buildFullPackage` and the statement's
  mandatory `claimedResult = result` conjunct are untouched, and no `redteam-status.json` `status`
  is flipped.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenBuildableAssembly
import Nock.RedTeam.Batch191Thm54ServedMemoryTraceInhabited

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch221

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _
noncomputable section

/-! ## 1. The three carried premises, discharged -/

/-- `Ksz = 64` is below the characteristic.  Together with `Batch180.dot_accAt_le`
(`accAt ≤ 24 ≤ 64`) and `Batch191.b191_hKsz2` (`2 · kMem = 20 ≤ 64`) this settles that the two
opposite-facing `Ksz` conditions are jointly satisfiable at this program. -/
theorem b221_hKszChar : (64 : ℕ) < ringChar DK := by
  rw [DotConfig769.ringChar_K]; norm_num

/-- The request IO column, `13` records, fits the `2^8` orbit with a slot to spare. -/
theorem b221_hprogCap :
    accAt (airReorder (dotTree (K := DK)))
        (bfsRows (airReorder (dotTree (K := DK)))).length + 1 ≤ 2 ^ executionOrbit.h := by
  rw [Batch211.b211_accAt_eq_13]; norm_num [executionOrbit]

/-- The memory table, `184` rows, likewise. -/
theorem b221_hmemCap :
    (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))).length + 1
      ≤ 2 ^ executionOrbit.h := by
  rw [Batch180.dot_memRowsLen]; norm_num [executionOrbit]

/-! ## 2. The term -/

/-- **`BuildableNockExecution` at the generated Tier A carrier.** -/
def b221Buildable
     :
    BuildableNockExecution DF DK :=
  genBuildableOfProgram (F := DF) (q := 769) (Λ := DotConfig769.Λ)
    seedZ alphaA seedZ_ne_zero two_ne_zero 0 0 0
    Batch216.b216Chal Batch180.dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    (Batch180.dot_seedGood _) (Batch180.dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) Batch180.dot_air_traceConfined
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
    (by have := Batch180.dot_accAt_le; omega)
    (by have := Batch180.dot_accAt_le; omega)
    Batch191.b191_hKsz2
    Batch180.dot_hb (by norm_num) DotConfig769.ringChar_K.symm Batch180.dot_haxis
    (Batch180.not_mem_badSeeds_of_pairs _ _ Batch180.dot_gen_pairs_sep)
    Batch180.dot_gen_hout
    b221_hKszChar b221_hprogCap b221_hmemCap Batch180.dot_hlt

/-! ## 3. The assembled object is the measured one -/



theorem b221_laterSeedZeros : BuildableAxisWitness.LaterSeedZeros b221Buildable :=
  genBuildableOfProgram_laterSeedZeros

theorem b221_q : b221Buildable.q = 769 := rfl

theorem b221_cfg : b221Buildable.cfg = Batch216.b216Cfg := rfl

theorem b221_exec : b221Buildable.exec = Batch216.b216Exec := rfl

theorem b221_semanticData : b221Buildable.semanticData = Batch216.b216Data := rfl

theorem b221_memoryTrace : b221Buildable.memoryTrace = Batch191.b191Mt := rfl

/-! ## 4. Non-vacuity, read off the assembled object

The `Nodup` field is a claim about a thirteen-element list of `GaloisField 769 3` vectors, and the
component that separates them is the timestamp — `alphaA^1 … alphaA^13`, distinct because
`13 < 192 = orderOf alphaA` (`Batch180.alphaA_order_eq_192`). -/

theorem b221_requestIO_length : b221Buildable.exec.derivedRequestIO.length = 13 := by
  show (genExactExecution (F := DF) Batch216.b216Chal 64 executionOrbit Batch216.b216_horb
      0 0 0 (genComputeRows seedZ alphaA (dotTree (K := DK)))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le
      Batch216.b216_mem_le).derivedRequestIO.length = 13
  rw [genExactExecution_derivedRequestIO_length (F := DF) seedZ alphaA Batch216.b216Chal 64
    executionOrbit Batch216.b216_horb 0 0 0 (dotTree (K := DK)) _
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le,
    Batch211.b211_accAt_eq_13]

/-- The eighth `encRec` coordinate of the assembled execution's request column is
`alphaA^1, …, alphaA^13`. -/
theorem b221_requestIO_ts :
    b221Buildable.exec.rawRequests.map (fun r => r.ts) =
      (List.range 13).map (fun i => alphaA ^ (i + 1)) := by
  show (genExactExecution (F := DF) Batch216.b216Chal 64 executionOrbit Batch216.b216_horb
      0 0 0 (genComputeRows seedZ alphaA (dotTree (K := DK)))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le
      Batch216.b216_mem_le).rawRequests.map (fun r => r.ts) = _
  rw [genExactExecution_rawRequests_ts (F := DF) seedZ alphaA Batch216.b216Chal 64
    executionOrbit Batch216.b216_horb 0 0 0 (dotTree (K := DK)) _
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le,
    Batch211.b211_accAt_eq_13]

/-- The structure's own `requestNodup` field, on a list the previous two theorems identify. -/
theorem b221_requestNodup : b221Buildable.exec.derivedRequestIO.Nodup :=
  b221Buildable.requestNodup

theorem b221_requestIO_ne_nil : b221Buildable.exec.derivedRequestIO ≠ [] := by
  intro hnil
  have := b221_requestIO_length
  rw [hnil] at this
  simp at this

/-! ## 5. The other four side conditions, read back -/

theorem b221_Ksz_lt_ringChar : b221Buildable.cfg.Ksz < ringChar DK :=
  b221Buildable.Ksz_lt_ringChar

theorem b221_progIOCapacity :
    b221Buildable.exec.derivedRequestIO.length + 1 ≤ 2 ^ b221Buildable.cfg.orbit.h :=
  b221Buildable.programIOCapacity

theorem b221_memIOCapacity :
    b221Buildable.exec.derivedResponseIO.length + 1 ≤ 2 ^ b221Buildable.cfg.orbit.h :=
  b221Buildable.memoryIOCapacity

theorem b221_recordCountBalance : RowLayout.RecordCountBalanced b221Buildable.exec :=
  b221Buildable.recordCountBalance

end
end Nock.RedTeam.Batch221

#print axioms Nock.RedTeam.Batch221.b221_hKszChar
#print axioms Nock.RedTeam.Batch221.b221_hprogCap
#print axioms Nock.RedTeam.Batch221.b221_hmemCap
#print axioms Nock.RedTeam.Batch221.b221Buildable
#print axioms Nock.RedTeam.Batch221.b221_memoryTrace
#print axioms Nock.RedTeam.Batch221.b221_requestIO_length
#print axioms Nock.RedTeam.Batch221.b221_requestIO_ts
#print axioms Nock.RedTeam.Batch221.b221_requestNodup
#print axioms Nock.RedTeam.Batch221.b221_requestIO_ne_nil
