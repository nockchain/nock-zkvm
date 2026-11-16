/-
  Nock/NockVMROM/Thm54/ResponseTsMemPowers.lean

  Response timestamps are α-powers outside the
  hostile failure event.

  Outside `optimizedFailureEvent`, hostile LIO identifies response records
  with requests.
  Every active request timestamp is `ln₀ · α^{S(i)+j+1}` with `ln₀ = 1`.
  Reducing the exponent mod `orderOf α` (needs `α ≠ 0`) puts every response
  `ts` in `⟨α⟩` below the order — the finder hyp of `memExponent`.

  `α ≠ 0` is discharged from the α-collision exclusion whenever there are at
  least two request slots (`0 ∈ TimestampCollisionEvent D` for `D ≥ 2`);
  with fewer slots it is an explicit hyp (the `D ≤ 1` edge: `orderOf 0 = 0`
  makes the finder form uninhabited at `ts = 0`).
-/
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
import Nock.NockVMROM.Thm54.HostileRecordLists
import Nock.NockVMROM.Thm54.ForestExponentOrderClosure
import Nock.IO
import Mathlib.GroupTheory.OrderOfElement
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.ResponseTsMemPowers

open scoped Polynomial
open Polynomial
open Nock
open Nock.IO
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure
open Nock.Framework
open MonolithicRAP

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Timestamp coordinate of an encoded memory record. -/
def recordTs (r : Fin 10 → K) : K := r 7

/-- A field element lies in `⟨α⟩` below `orderOf α`. -/
def MemPower (α ts : K) : Prop :=
  ∃ e : ℕ, e < orderOf α ∧ α ^ e = ts

/-- Reduce any power to a representative below the order. -/
theorem memPower_of_pow {α : K} (hα : α ≠ 0) (n : ℕ) :
    MemPower α (α ^ n) := by
  have hpos : 0 < orderOf α := orderOf_pos_of_ne_zero hα
  refine ⟨n % orderOf α, Nat.mod_lt n hpos, ?_⟩
  rw [pow_mod_orderOf]

theorem zero_mem_timestampCollisionEvent {D : ℕ} (hD : 2 ≤ D) :
    (0 : K) ∈ TimestampCollisionEvent D := by
  rw [mem_timestampCollisionEvent]
  refine ⟨1, ?_, 2, ?_, by norm_num, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
  · exact Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
  · simp [zero_pow (by norm_num : (1 : ℕ) ≠ 0),
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Outside the collision event with at least two requests, `α ≠ 0`. -/
theorem alpha_ne_zero_of_not_collision {D : ℕ} {α : K}
    (hα : α ∉ TimestampCollisionEvent D) (hD : 2 ≤ D) : α ≠ 0 := by
  intro h0
  apply hα
  rw [h0]
  exact zero_mem_timestampCollisionEvent hD

/-- Active request timestamps are α-powers. -/
theorem request_ts_mem_powers
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
    (hα0 : alphaM c.1 ≠ 0)
    (r : Fin 10 → K)
    (hr : r ∈ OptimizedComputeHostileAccumulator.hostileRequests P Qc) :
    MemPower (alphaM c.1) (recordTs r) := by
  obtain ⟨i, j, hact, hrfl⟩ := mem_hostileRequests P Qc hr
  have hts :=
    rowRecord_ts_at P Qc hacc.compute_satisfies hchar hz0 i j hact
  have hln : ln0 P Qc = 1 := hostile_ln0_eq_one P Qc hacc.compute_satisfies
  have hαeq : chipAlpha P = alphaM c.1 := chipAlpha_eq_alphaM P Qc Qm c hacc
  have hpow : rowRecord (rowEnv P Qc i) j 7 = alphaM c.1 ^ expOf P Qc i j := by
    rw [hts, hln, one_mul, hαeq]
  rw [hrfl, recordTs, hpow]
  exact memPower_of_pow hα0 _

/-- Response timestamps are α-powers outside the hostile failure event, under `α ≠ 0` (finder form of `memExponent`). -/
theorem response_ts_mem_powers {Ksz : ℕ}
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecords Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (P.hostileRequests Qc).length)
    (hKresp : (P.hostileResponses Qm).length ≤ Ksz)
    (hα0 : alphaM c.1 ≠ 0)
    (r : Fin 10 → K)
    (hr : r ∈ OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :
    MemPower (alphaM c.1) (recordTs r) := by
  have hcomp := P.optimizedFailureEvent_good_components Qc Qm c hgood
  have hα : alphaM c.1 ∉ TimestampCollisionEvent (P.hostileRequests Qc).length :=
    hcomp.2.2.1
  have hnot : ¬ (c.2.1.1 ∈ FiniteIO.IORLCCollisionEvent (P.hostileRecords Qc Qm) ∨
      c.2.1.2 ∈ FiniteIO.IOPoleHitEvent (P.hostileRecords Qc Qm) c.2.1.1 ∨
      c.2.1.2 ∈ FiniteIO.IOLogDerivEvent (P.hostileRecords Qc Qm) c.2.1.1) := by
    intro h
    apply hio
    simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hlio : IO.LIO Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) := by
    have hKreq' : IO.InRange Ksz
        (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length := by
      simpa [hostileRequests_eq_package] using hKreq
    have hKresp' : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz := by
      simpa [hostileResponses_eq_package] using hKresp
    have hα' : alphaM c.1 ∉ TimestampCollisionEvent
        (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length := by
      simpa [hostileRequests_eq_package] using hα
    have hrec : hostileRecords P Qc Qm = P.hostileRecords Qc Qm :=
      hostileRecords_eq_package P Qc Qm
    have hnot' : ¬ (c.2.1.1 ∈ FiniteIO.IORLCCollisionEvent (hostileRecords P Qc Qm) ∨
        c.2.1.2 ∈ FiniteIO.IOPoleHitEvent (hostileRecords P Qc Qm) c.2.1.1 ∨
        c.2.1.2 ∈ FiniteIO.IOLogDerivEvent (hostileRecords P Qc Qm) c.2.1.1) := by
      simpa [hrec] using hnot
    exact hostile_LIO' P Qc Qm c hacc hchar (hz0_of_good P Qc Qm c hacc hgood) hα'
      hKp hKreq' hKresp'
      (fun h => hnot' (Or.inr (Or.inl h))) (fun h => hnot' (Or.inl h))
      (fun h => hnot' (Or.inr (Or.inr h)))
  have hperm : (OptimizedComputeHostileAccumulator.hostileRequests P Qc).Perm
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :=
    hlio.2.2
  have hrq : r ∈ OptimizedComputeHostileAccumulator.hostileRequests P Qc :=
    (List.Perm.mem_iff hperm).2 hr
  exact request_ts_mem_powers P Qc Qm c hacc hchar
    (hz0_of_good P Qc Qm c hacc hgood) hα0 r hrq

/-- The two-request discharge of `α ≠ 0` from the priced α-collision event. -/
theorem alphaM_ne_zero_of_good_two
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hD : 2 ≤ (P.hostileRequests Qc).length) :
    alphaM c.1 ≠ 0 :=
  alpha_ne_zero_of_not_collision
    (P.optimizedFailureEvent_good_components Qc Qm c hgood).2.2.1 hD

/-- Convenience: response powers when `|hostileRequests| ≥ 2` (no extra `α ≠ 0`). -/
theorem response_ts_mem_powers_of_two {Ksz : ℕ}
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (P.hostileRecords Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (P.hostileRequests Qc).length)
    (hKresp : (P.hostileResponses Qm).length ≤ Ksz)
    (hD : 2 ≤ (P.hostileRequests Qc).length)
    (r : Fin 10 → K)
    (hr : r ∈ OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :
    MemPower (alphaM c.1) (recordTs r) :=
  response_ts_mem_powers P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp
    (alphaM_ne_zero_of_good_two P Qc Qm c hgood hD) r hr

end

end Nock.NockVMROM.Thm54.ResponseTsMemPowers

#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers
#print axioms Nock.NockVMROM.Thm54.ResponseTsMemPowers.response_ts_mem_powers_of_two
