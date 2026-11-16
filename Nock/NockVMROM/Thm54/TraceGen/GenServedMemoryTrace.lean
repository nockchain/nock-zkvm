/-
  Nock/NockVMROM/Thm54/TraceGen/GenServedMemoryTrace.lean

  Four fields, each landed separately and each a discharge rather than a reduction:

  | field | source |
  |---|---|
  | `roots` | `genRoots` |
  | `timestampPowersNodup` | `genRoots_timestampPowersNodup` (`FW`) |
  | `forestIndexRange` | `genRoots_forestIndexRange` (`FU` §2) |
  | `semanticCoverage` | `genSemanticData_semanticCoverage` (`FY`) |

  **Scope.**  `∀ program accepted by `genComputeSkeleton``, at arbitrary field, seed, `α`, challenge
  vector and coins.

  `genRoots` itself takes an arbitrary `inp`; this assembly does not, because
  `genSemanticData`'s `hmi` fixes it.

  **The premises, and that there are no new ones.**  This definition adds nothing beyond what
  `genSemanticData` already carries plus one `Ksz` choice:

  * `horbα` is **implied** by the `hB`/`hwin` window premise `genSemanticData` carries
    (`horb_of_window`, `FU.2` §1), so it is not additional — and it is met by an explicit witness at
    Goldilocks (`FV`).  It earns its keep twice: the chain arm's `hne` (`FH`) and, less obviously,
    making the timestamp a usable key for `semanticCoverage`, since `α ^ ·` is injective only below
    `orderOf α` (`FY`).
  * `hKsz2 : 2 * kMem ≤ Ksz` is a compiler choice — `Ksz` is free in `genExactConfig` and `2 * kMem`
    is computable by the generator (`FU` §2).
  * everything else is `genSemanticData`'s own, unchanged.

  **What this does *not* do.**  It does not produce a `BuildableNockExecution`, a `Data`, an
  `Inputs`, or the capstone.  `genBuildable` (`GenExactExecution.lean:171`) still wants `hnodup` and
  `hbal` — `hbal` is `genBuildable_hbal` (`FF`), `hnodup` is not composed — and `Data`'s sixteen
  fields and the statement's mandatory `claimedResult = result` conjunct are untouched.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenForestTimestampNodup
import Nock.NockVMROM.Thm54.TraceGen.GenServedSemanticCoverage

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-- **`mt` for any accepted program.**

The hypothesis list is `genSemanticData`'s plus `hKsz2`; see the module docstring for why `horbα`
is not an addition -/
noncomputable def genServedMemoryTrace {q Λ : ℕ} [Fintype K] [DecidableEq K]
    (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hinp : chal.computeInputs = ⟨α, z, a, b, c⟩)
    (hmi : chal.memoryInputs = memInputs z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hseed : SeedGood z t)
    (hcoins : ComputeCoinsGeneric z α a b c (airReorder t))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (B : ℕ) (hB : B ≤ orderOf α)
    (hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B)
    (hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz)
    (hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)))
    (hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    ExactServedMemoryTrace q Λ
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genSemanticData (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hb hq hchar
        haxis hbad hout hfirst)
      (genExactExecutionA (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) where
  roots := genRoots (F := F) z α a b c chal (congrArg ComputeTable.Inputs.z hinp)
    (congrArg ComputeTable.Inputs.α hinp) Ksz orbit horb (memInputs z) h
    (horb_of_window hB hwin) hmempos hcomp hmem
  timestampPowersNodup :=
    genRoots_timestampPowersNodup (F := F) z α a b c chal
      (congrArg ComputeTable.Inputs.z hinp) (congrArg ComputeTable.Inputs.α hinp)
      Ksz orbit horb (memInputs z) h (horb_of_window hB hwin) hmempos hcomp hmem
  forestIndexRange :=
    genRoots_forestIndexRange (F := F) z α a b c chal
      (congrArg ComputeTable.Inputs.z hinp) (congrArg ComputeTable.Inputs.α hinp)
      Ksz orbit horb (memInputs z) h (horb_of_window hB hwin) hmempos hcomp hmem hKsz2
  semanticCoverage :=
    genSemanticData_semanticCoverage (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
      Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hb hq hchar
      haxis hfirst
      hbad hout

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genServedMemoryTrace
