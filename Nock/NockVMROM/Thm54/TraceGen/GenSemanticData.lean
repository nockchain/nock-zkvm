/-
  Nock/NockVMROM/Thm54/TraceGen/GenSemanticData.lean

  Three fields:

  * `rowAccepted` — `genRowAccepted` (`GenSemanticDataParts.lean`, `EG`);
  * `rows` — assembled here, one `ComputeRowSemanticData` per index from
    `ComputeRowSemanticData.ofSkeleton` (`BoundSemanticTrace.lean:967`).

  `ofSkeleton` takes nine arguments and every one of them now exists generically:
  `S`, `exec`, `binds` (`EB`), `C` (`ED`, a field projection), `hb`, `hcmp` (here), `hgood`, `hop`
  (`ED`), `i`.  The only genuinely new content in this module is `genComparisonBounded`; the rest
  is threading.

  **The side conditions, all of which are the compiler's and none of which are hidden.**  The
  signature below is long on purpose: every hypothesis is a stated precondition of `nockCompiles`
  rather than an assumption buried in a definition.  Three are *counted seed events*, independent of
  each other and each with its own generic bound (`EA`, `ED`):

  * `SeedGood z t` — the three `V_comp` conditions (`GenDyckBadSeed`, `DD`–`DG`);
  * `hout : z ∉ sizeWindowFailureSeeds …` — the OP3/OP4/OP6 size windows;
  * `hbad : z ∉ ….census.badSeeds` — NPR fingerprint collisions between census comparison operands
    (`JointSoundness.lean:274`), which feeds `PairFaithful`.

  **Do not try to derive one from another** — they are built from different data and none contains
  the others (`EA`, and `ED`'s wording correction in `EP.1`).

  Also carried: `hb : S.BoundedBy q` — taken **directly**, not via `CanonicalCommitmentCheck`, which
  has no witness at a generated trace (`EP.1`, `EP.2`); `SkeletonAxisRange`, declared and witnessed
  at `Batch168` (`EC`); and `hmi`, which pins `β = γ = 0` — disclosed, pre-existing, and sound for
  the reason `Batch170` compiles (`EM`).

  **Scope.**  `∀ program accepted by `genComputeSkeleton``, at arbitrary field, seed, `α`, challenge
  vector and coins.  Never `∀ E`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.Framework.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

variable {lmb : K}

/-! ## `hcmp` — comparison operands are bounded

`skeletonComparisons_pair_bounded` (`GenericHonestData.lean:2713`) is the per-row form and was
already generic; `SkeletonComparisonBoundedBy` is exactly its pointwise closure. -/

/-- **`SkeletonComparisonBoundedBy` from the skeleton bound and the axis range.**  The same two
inputs `genCombinedBounded` takes, at the per-comparison level `ofSkeleton` wants. -/
theorem genComparisonBounded {q : ℕ} {S : SemanticSkeleton}
    (hb : S.BoundedBy q) (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q S) :
    SkeletonComparisonBoundedBy K q S := by
  intro s hs c hc
  exact GenericHonestData.skeletonComparisons_pair_bounded
    ((List.forall_iff_forall_mem.mp hb.computeRows) s hs) hq hchar
    (haxis s hs).1 (haxis s hs).2 hc

/-! ## `rows`, and `sd` -/

section Assembly

variable [Fintype K] [DecidableEq K]

/-- **`ExactExecutionSemanticData.rows` for any accepted program.**

One `ComputeRowSemanticData` per index, from `ofSkeleton` with all nine arguments supplied. -/
noncomputable def genRows {q Λ : ℕ} (z α : K) (hz : z ≠ 0) (a b c : K)
    (chal : ChallengeVector K) (hzc : chal.z = z)
    (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h)
    (hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q)
    (hq : 11 < q) (hchar : q = ringChar K)
    (haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)))
    (hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds)
    (hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))) :
    ∀ i, SemanticTrace.ComputeRowSemanticData q Λ
      ((genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).computeRowAt i) :=
  fun i =>
    SemanticTrace.ComputeRowSemanticData.ofSkeleton _ _
      (genBindsAt_threaded (F := F) z α (memInputs z) chal hzc Ksz orbit horb a b c h
        hmempos hcomp hmem)
      (genSkeletonP8Census hΛ h hconf _)
      hb
      (genComparisonBounded hb hq hchar haxis)
      hbad
      (genOperationalPremises hchar hz h _ hout)
      i

/-- Long signature on purpose: every hypothesis is a stated precondition of `nockCompiles`, not an
assumption buried in a definition.  See the module docstring for which are counted seed events and
why none can be derived from another. -/
noncomputable def genSemanticData {q Λ : ℕ} (z α : K) (hz : z ≠ 0) (htwo : (2 : K) ≠ 0) (a b c : K)
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
    (hlt : ∀ n, InTree (bfsAssign (airReorder t)) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K) :
    SemanticTrace.ExactExecutionSemanticData q Λ
      (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem)
      (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem) where
  language := genLanguage (F := F) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed
    hcoins hmempos hcomp hmem B hB hwin hKsz hb hlt
  rowAccepted := genRowAccepted (F := F) z α hz a b c chal hinp Ksz orbit horb h hseed _
    hmempos hcomp hmem
  rows := genRows (F := F) z α hz a b c chal (congrArg ComputeTable.Inputs.z hinp)
    Ksz orbit horb h hΛ hconf hmempos hcomp hmem hb hq hchar haxis hbad hout

end Assembly

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComparisonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genRows
#print axioms Nock.NockVMROM.Thm54.TraceGen.genSemanticData
