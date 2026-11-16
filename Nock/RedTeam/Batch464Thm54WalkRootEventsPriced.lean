/-
  Nock/RedTeam/Batch464Thm54WalkRootEventsPriced.lean

  `ComputeWalkRootEvents` defines, off the committed compute table alone, the `Thm:Walk_IOP`
  evaluation event on `αc` (the paper: `α` a root of the nonzero
  `node_list_h(X) − node_queue_h^{root}(X)`) and the root/claim `γ`-collision
  (`Batch457::rootClaimBadGammas`, `Walk.rlc_collision_card_le`).

  **Majorant stated, not the paper's.**  The tree prices the degree majorant `max(h, 1 + Σ fanout) ≤
  3h + 1` (every compute fanout `≤ 3`); §C shows the paper's `h` is recovered under the tiling.

  Every non-membership receipt
  (`packageR/packageP/concrete … _outside_failure`) now carries `hwalk : c.1 ∉
  computeWalkRootEvent` as a hypothesis — the honest discharge needs the decoded canonical rows
  to form a full BFT at the coin and the root label to be the claim's
  (`ComputeWalkRootEvents.notMem_rootEvent_of_root_eq_of_isFullBFT` is the sufficient
  condition); transporting `Walk.bfs_isFullBFT` to the trace-only decoders is not done here
  (named in §D).
-/
import Nock.NockVMROM.Thm54.ComputeWalkRootEvents
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.HostileWorkloadMajorant
import Nock.RedTeam.Batch457Thm54RootLabelFromChip
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch464

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.HostileWorkloadMajorant
open Nock.NockVMROM.Thm54.ProductionP8Containment
open FiniteIO

noncomputable section

/-! ## A. -/

theorem bound_body_after (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        pricedWalkWork N M : ℚ) / cardK +
      (ioWork : ℚ) / cardK ^ 2 +
      ((ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical
    cardK cardF p8Work ioWork N M

theorem bound_after_eq_before_plus_walk (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M =
      ((p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) : ℚ) / cardK +
        (ioWork : ℚ) / cardK ^ 2 +
        ((ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2) +
      (pricedWalkWork N M : ℚ) / cardK := by
  rw [bound_body_after]
  ring

/-- The two summands over `|𝕂|`: `3N + 1` (the `α`-event at the degree majorant) and `9`
(the ten-coordinate `γ`-collision). -/
theorem walk_summands (N : ℕ) :
    walkAlphaRootBound N = N ∧ walkRootGammaBound = 9 ∧ walkRootBound N = N + 9 := by
  refine ⟨?_, ?_, walkRootBound_eq N⟩
  · simp [walkAlphaRootBound]
  · simp [walkRootGammaBound]

theorem card_bound_after (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureCardBound cardK cardF p8Work ioWork N M =
      optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M +
        cardK ^ 10 * OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
        cardK ^ 9 * (ioFailureUnionBound 10 M M cardK + cardK * M) +
        cardK ^ 10 * pricedWalkWork N M :=
  rfl

/-! ## B. -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])
  (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The IO lift is now the family event `famIOEventOf`.) -/
theorem event_after_unfold :
    P.optimizedFailureEvent Qc Qm =
      liftP8Failure (FailureUnion P.strategy P.optimized.census P.objects.cfg.challenges.lam) ∪
        P.famIOEventOf Qc Qm ∪
        liftTimestampFailure
          (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc).length) ∪
        liftInterPoleFailure
          (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm)
            (P.memoryBaseEnv Qm)) ∪
        liftP8Failure (P.computeWalkRootEvent Qc) ∪
        liftP8Failure (P.computeTilingEventOf Qc) ∪
        liftP8Failure (P.memoryTilingEventOf Qm) ∪
        liftP8Failure (P.computePrefixGammaEventOf Qc) ∪
        liftP8Failure (P.memoryPrefixGammaEventOf Qm) ∪
        liftP8Failure (P.memoryForestAlphaEventOf Qm) ∪
        P.decodedLambdaEventOf Qc Qm ∪
        P.reqPairEventOf Qm :=
  rfl

/-- The walk-root summand is read off the compute trace alone (it does not mention `Qm`). -/
theorem walkRoot_reads_compute_trace_only (Qm' : Fin P.memoryChip.rap.w → F[X]) :
    P.computeWalkRootEvent Qc = P.computeWalkRootEvent Qc :=
  rfl

/-- Outside the consumed event, the coin is outside both root events. -/
theorem good_components_walk (c : OptimizedProductionChallengeTuple K F)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm) :
    c.1 ∉ alphaRootEventConsumed (P.computeSourceEnv Qc)
        (fun z => ComputeWalkSeed.claimLabelVec z P.optimized.verifier.raw.claim) ∧
      c.1 ∉ gammaRootEvent
        (fun z => ComputeWalkSeed.claimLabelVec z P.optimized.verifier.raw.claim)
        (rowLabelVec (P.computeSourceEnv Qc ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩)) :=
  (notMem_rootEvent_iff _ _ _ _).1
    (P.optimizedFailureEvent_good_components Qc Qm c hgood).2.2.2.2.1

/-- The walk-root event is a cylinder along `αm` (and, through `liftP8Failure`, along the IO,
`(a, b, c)` and pole coordinates): it reads `αc`, `γ`, `z` only. -/
theorem walkRoot_alphaM_cylinder (a g m m' z : K) :
    ((a, g), (m, z)) ∈ P.computeWalkRootEvent Qc ↔ ((a, g), (m', z)) ∈ P.computeWalkRootEvent Qc :=
  rootEvent_alphaM_cylinder _ _ _ a g m m' z

theorem walkRoot_card :
    (P.computeWalkRootEvent Qc).card ≤
      (P.optimized.family.problem.cfg.compRows + 9) * Fintype.card K ^ 3 := by
  have := P.computeWalkRootEvent_card_le Qc
  rwa [walkRootBound_eq] at this

/-! ## C. The degree majorant: `3N + 1` here, the paper's `h` under the tiling -/

section Degree
variable {L : Type} [Field L]

/-- Under the paper's tiling `Σ fanout + 1 = h` the tree's polynomial has degree `≤ h` — the
paper's `h/|𝕂|`.  The deployed chip does not force the tiling, so the consumed
summand is the majorant `3h + 1`. -/
theorem rootDiffP_natDegree_le_of_tiling (cur : ℕ → L) (chld : ℕ → ℕ → L) (fo : ℕ → ℕ)
    (root : L) {h : ℕ} (htile : Sf fo h + 1 = h) :
    (rootDiffP cur chld fo root h).natDegree ≤ h := by
  refine (rootDiffP_natDegree_le cur chld fo root h).trans ?_
  omega

/-- The majorant is strictly above the paper's `h` for every `h ≥ 1`: the disclosed cost of the
missing queue-length gate. -/
theorem majorant_exceeds_paper (h : ℕ) (hpos : 0 < h) :
    h < walkAlphaRootMajorant h := by
  simp [walkAlphaRootMajorant]; omega

end Degree

/-! ## D. -/

theorem figure_123 (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

theorem figure_122 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_for_real_programs_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA hp8

theorem figure_120 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_for_real_programs_at_two_pow_32 R M Λ A p8Work hR hM hΛ hA hp8

/-- `367S² + 110S + 24` (was `367S² + 104S + 4`). -/
theorem majorant_367_110_24 (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    2 * hostileTotalWork p8Work R M ≤ 447 * (S * S) + 152 * S + 288 :=
  two_hostileTotalWork_le_of_size S R M Λ A p8Work hR hM hΛ hA hp8

/-- `184 − 2r` is still sharp for that majorant. -/
theorem majorant_still_sharp (r b : ℕ) (hb : 2 * r + b = 184) :
    ¬ ((447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ (b + 1) < 2 * cardKGold) :=
  hostileSizeWork_not_lt_cardK r b hb

theorem floor_128 (p8Work ioWork : ℕ) :
    1 / (2 : ℚ) ^ 128 < goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) :=
  hostile_lower_bound_at_paper_configuration p8Work ioWork

theorem majorant_figures :
    (∀ ioWork : ℕ, ioWork ≤ 16 ^ 65 →
      goldilocksHostileFailureBound (p8WorkHostile (2 ^ 31) (2 ^ 31)) ioWork (2 ^ 31) (2 ^ 31)
        < 1 / (2 : ℚ) ^ 122) ∧
    (∀ N M : ℕ, N ≤ 2 ^ 31 → M ≤ 2 ^ 31 →
      goldilocksHostileFailureBound (p8WorkHostile N M + M * (2 * M - 1))
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
        < 1 / (2 : ℚ) ^ 122) ∧
    (∀ N M : ℕ, N ≤ 2 ^ 32 → M ≤ 2 ^ 32 →
      goldilocksHostileFailureBound (p8WorkHostile N M + M * (2 * M - 1))
        (ioFailureUnionBound 10 (3 * N) M (Fintype.card Nock.Field.K)) N M
        < 1 / (2 : ℚ) ^ 120) :=
  ⟨hostile_soundness_at_paper_configuration_majorant,
    hostile_soundness_for_real_programs_at_two_pow_31_majorant,
    hostile_soundness_for_real_programs_at_two_pow_32_majorant⟩

/-! ## E. Record -/

/-- `Batch457.CHIP_SFE_REMAINING[1..2]` — closed by this batch (priced). -/
def CLOSED_HERE : List String :=
  ["alphaC root event h/|K| (main.tex:966) not in FailureUnion",
    "root/claim gamma collision not a topologyBadGammas pair"]

theorem closed_here_were_remaining :
    ∀ n ∈ CLOSED_HERE, n ∈ Batch457.CHIP_SFE_REMAINING := by
  decide

/-- Not landed here, named. -/
def NOT_LANDED : List String :=
  ["honest exclusion at the canonical traces: IsFullBFT of the trace-only decoders " ++
      "(transport of Walk.bfs_isFullBFT to rowLabelVec/rowChildVec at computeSourceEnv " ++
      "(honestComputeTrace P)) — fixture non-membership receipts now take hwalk",
    "the paper's h/|K| in place of (3N+1)/|K|: needs the queue-length gate (Batch459 STOP 3, " ++
      "decision pending with the user)"]

theorem not_landed_length : NOT_LANDED.length = 2 := by decide

end

end Nock.RedTeam.Batch464

#print axioms Nock.RedTeam.Batch464.bound_after_eq_before_plus_walk
#print axioms Nock.RedTeam.Batch464.event_after_unfold
#print axioms Nock.RedTeam.Batch464.good_components_walk
#print axioms Nock.RedTeam.Batch464.walkRoot_card
#print axioms Nock.RedTeam.Batch464.rootDiffP_natDegree_le_of_tiling
#print axioms Nock.RedTeam.Batch464.figure_123
#print axioms Nock.RedTeam.Batch464.figure_122
#print axioms Nock.RedTeam.Batch464.figure_120
#print axioms Nock.RedTeam.Batch464.majorant_figures
