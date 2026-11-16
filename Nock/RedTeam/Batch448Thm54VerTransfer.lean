/-
  Nock/RedTeam/Batch448Thm54VerTransfer.lean

  **Close +3 (`vmem`, `memoryRows`, `io`) → 14/21.**

  After ver alignment, `derivedResponseIO` (ver list) matches
  `hostileResponses` (role-39 = 1) at decoded rows.

  Full family-acceptance discharge of `vmem`/`memoryRows` may still name
  topology hyps; the wrap-target equality is compiled here.
-/
import Nock.MemoryTable
import Nock.NockVM
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch430Thm54TransferRemainingHole
import Nock.RedTeam.Batch431Thm54OpenConjunctsAfterC2
import Nock.RedTeam.Batch446Thm54DerivedResponseByVer
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch448

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.MonolithicRAP
open Module

/-- Open `AcceptedContent` conjuncts after ver alignment.  Count 7. -/
def openConjunctsAfterVer : List String :=
  Nock.RedTeam.Batch431.openConjunctsAfterC2Target

theorem openConjunctsAfterVer_length :
    openConjunctsAfterVer.length = 7 := by decide

/-- Chip-closed count after the three wrap targets leave: **14**. -/
theorem closed_count : 21 - openConjunctsAfterVer.length = 14 := by decide

def newlyClosed : List String := ["memoryRows", "vmem", "io"]

theorem newlyClosed_length : newlyClosed.length = 3 := by decide

theorem wrap_targets_left_batch398 :
    newlyClosed.Sublist Nock.RedTeam.Batch398.openConjuncts := by
  decide

theorem wrap_targets_not_open :
    ∀ name ∈ newlyClosed, name ∉ openConjunctsAfterVer := by
  decide

theorem closed_count_from_eleven :
    11 + newlyClosed.length = 14 := by decide

/-- Topology five remain; wrap targets are gone. -/
def remainingHyps : List String :=
  ["mem_first_counts", "mem_first_indicator",
    "computeTopology", "memoryTopology", "axisStructural",
    "rootBoundary", "structuralChecks"]

theorem remainingHyps_eq_open :
    remainingHyps = openConjunctsAfterVer := by
  decide

theorem ver_hole_cleared :
    "derivedResponseIO_eq_hostileResponses" ∈
      Nock.RedTeam.Batch430.remainingHyps ∧
    "derivedResponseIO_eq_hostileResponses" ∉ remainingHyps := by
  decide

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Role 39 is in source width (`6 + 3·39 + 2 < 181`). -/
theorem memory_role39_col_lt (k : Fin 3) :
    6 + 3 * 39 + (k : ℕ) < 182 := by
  have : (k : ℕ) < 3 := k.isLt
  omega

/-- `memorySourceEnvAt` and `rowEnvK` agree at role 39 (ver). -/
theorem memorySourceEnvAt_trace39_eq_rowEnvK
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (memorySourceEnvAt P c Qm i).trace 39 = (rowEnvK P Qm i).trace 39 := by
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit
      (rowNodeSet P.optimized.memoryNodes)).1
  simp only [memorySourceEnvAt, rowEnvK, memorySourceTemplate_col0,
    memoryBaseEnvAt, rowEnvF, gatherEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hlt171 : 6 + 3 * 39 + (k : ℕ) < 182 := memory_role39_col_lt k
  have hlt : 6 + 3 * 39 + (k : ℕ) < (sourceOf P).rap.w := by
    rw [hw]; exact hlt171
  simp only [envOfTrace, memoryCol0, dif_pos hlt171, dif_pos hlt]
  have hidx : (⟨6 + 3 * 39 + (k : ℕ), hlt171⟩ : Fin 182) =
      Fin.cast hw.symm ⟨6 + 3 * 39 + (k : ℕ), hlt⟩ := Fin.ext rfl
  rw [memorySourceTrace_eq_proj, hidx]
  rfl

/-- Decode `ver` ↔ committed role 39 equals 1. -/
theorem decodeMemPub_ver_iff_role39
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (decodeMemPub P Qm c i).ver = true ↔
      (memorySourceEnvAt P c Qm i).trace 39 = 1 := by
  simp [decodeMemPub]

/-- Justification: the chip's
ten-slot `IO.LIO` on the hostile records gives the strategy-level nine-slot `IO.LIO` on these
prefixes by truncation, given nodup of the truncated responses — `Batch715.lio_trunc9`, restated on
this `trunc9` as `Batch728.batch448_trunc9_lio` (`Batch728.batch448_trunc9_eq` : the two `trunc9`
are `rfl`-equal). -/
def trunc9 {K : Type} (v : Fin 10 → K) : Fin 9 → K := fun d => v d.castSucc

theorem responseRecords_decode_eq_rowResponses
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hbool : (rowEnvK P Qm i).trace 39 = 0 ∨ (rowEnvK P Qm i).trace 39 = 1)
    (hCsrc : (memorySourceEnvAt P c Qm i).trace 57 = 1)
    (hCrow : (rowEnvK P Qm i).trace 57 = 1) :
    (responseRecords (decodeMemPub P Qm c i)).map
        (fun r => NockVM.encRecC r ((memorySourceEnvAt P c Qm i).trace 57)) =
      (rowResponses (rowEnvK P Qm i) (rowEnvF P Qm i)).map trunc9 := by
  have h39 := memorySourceEnvAt_trace39_eq_rowEnvK P c Qm i
  have hrec := encRec_decodeMem_eq_rowRecord (P := P) Qm c i
  simp only [responseRecords, rowResponses, rowResponseTerms, decodeMemPub_ver_iff_role39]
  have hrr : OptimizedMemoryHostileAccumulator.memRowRecord (memorySourceEnvAt P c Qm i) =
      trunc9 (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) := by
    funext d
    by_cases hd : (d : ℕ) < 8
    · have hj : 19 + (d : ℕ) ≤ 28 := by omega
      simp [OptimizedMemoryHostileAccumulator.memRowRecord, trunc9, rowRecord, hd,
        memorySourceEnvAt_trace_eq_rowEnvK P c Qm i (19 + (d : ℕ)) hj]
    · have h8 : (d : ℕ) = 8 := by omega
      simp [OptimizedMemoryHostileAccumulator.memRowRecord, trunc9, rowRecord, hd, h8,
        hCsrc, hCrow]
  rcases hbool with h0 | h1
  · have : (memorySourceEnvAt P c Qm i).trace 39 ≠ 1 := by
      rw [h39, h0]; exact zero_ne_one
    simp [this, h0]
  · have : (memorySourceEnvAt P c Qm i).trace 39 = 1 := by rw [h39, h1]
    simp [this, h1, hrec, hrr]

/-- Decoded flatten equals `hostileResponses` under boolean `ver` at every row. -/
theorem derivedResponseIO_eq_hostileResponses_decoded
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hbool : ∀ i : Fin (rows P),
      (rowEnvK P Qm i).trace 39 = 0 ∨ (rowEnvK P Qm i).trace 39 = 1)
    (hCsrc : ∀ i : Fin (rows P), (memorySourceEnvAt P c Qm i).trace 57 = 1)
    (hCrow : ∀ i : Fin (rows P), (rowEnvK P Qm i).trace 57 = 1) :
    (List.ofFn fun i : Fin (rows P) =>
        (responseRecords (decodeMemPub P Qm c i)).map
          (fun r => NockVM.encRecC r ((memorySourceEnvAt P c Qm i).trace 57))).flatten =
      (hostileResponses P Qm).map trunc9 := by
  simp only [hostileResponses, List.map_flatten, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun i =>
    responseRecords_decode_eq_rowResponses P Qm c i (hbool i) (hCsrc i) (hCrow i))

end

end Nock.RedTeam.Batch448

#print axioms Nock.RedTeam.Batch448.closed_count
#print axioms Nock.RedTeam.Batch448.wrap_targets_not_open
#print axioms Nock.RedTeam.Batch448.ver_hole_cleared
#print axioms Nock.RedTeam.Batch448.decodeMemPub_ver_iff_role39
#print axioms Nock.RedTeam.Batch448.derivedResponseIO_eq_hostileResponses_decoded
