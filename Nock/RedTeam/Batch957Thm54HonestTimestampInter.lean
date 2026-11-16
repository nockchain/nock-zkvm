/-
  Nock/RedTeam/Batch957Thm54HonestTimestampInter.lean

  **Component 3.**  `Batch909.HonestEventResidual` discharges it through `alphaOrder :
  3 * compRows ≤ orderOf α`, which the generator does NOT give (`hwin` bounds `programAcc`, the
  number of records, not `3 * compRows`).  It is not needed: the canonical request list IS the
  derived request list (`OptimizedCanonicalHostileLists.canonical_hostileRequests`), so its length
  is `derivedRequestIO.length`, and `α ≠ 0`, `derivedRequestIO.length ≤ orderOf α` suffice
  (`timestamp_honest`).  At the generated carrier `derivedRequestIO.length = programAcc`
  (`genExactExecution_derivedRequestIO_length`) and both premises are `hwin`.  Status: **proved**,
  no coin choice beyond the §1 binder `α` itself.

  **Component 4.**  `canonical_inter_not_hostile_failure` takes `interNe`, `interGamma8`,
  `inactiveMem`, `inactiveCprime`, `hC`.
  * `inactiveMem` is a theorem at every accepted execution (`eqBlk` forces `mem = MemRec.zero` on
    `decompose` / `halt`), hence at every buildable package (`inactiveMem_buildable`);
  * `interNe` holds at every package built from `inputsOfCarrier` (`interPoleOfE_ne_zero`);
  * `interGamma8` is **NOT implied** by the generator's choice: `interPoleOfE` avoids only the
    nine/ten-slot pole-hit events of the ACTIVE in-table records and `0`
    (`BuildableChips.exists_interPole_of_E`), and the padding rows' record RLC is `γ^8`
    (`rlc_encRecC_memRec_zero`), which is not among them.  So the generated package's pole may
    equal `-γ^8`, and then the honest pair lies in `allRowPoleHitEvent`.
-/
import Nock.RedTeam.Batch909Thm54R4HonestInstance
import Nock.NockVMROM.Thm54.TraceGen.GenCarrierInputs
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch957

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.OptimizedComputeSameExecution

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-! ## Component 3 -/

/-- The canonical compute trace commits exactly the derived request list. -/
theorem hostileRequests_canonical_length {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    (H : HonestFill P) :
    (P.hostileRequests (canonicalComputeTrace P)).length =
      P.optimized.family.problem.exec.derivedRequestIO.length := by
  have h := OptimizedCanonicalHostileLists.canonical_hostileRequests P H.hax H.hwidth
  have h' : P.hostileRequests (canonicalComputeTrace P) =
      (honestRecords10 P.optimized.family).requests := h
  rw [h', honestRecords10, RecordCarrier.extRecords_requests,
    List.length_map]

/-- **Component 3 at the honest instance, at any package**: `α ≠ 0` and the honest record
count below `orderOf α` (not `3 · compRows`). -/
theorem timestamp_honest {P : OptimizedFullStrictNockVMROMPackage F K hOrb} (H : HonestFill P)
    (hα0 : alphaM P.honestTuple.1 ≠ 0)
    (hord : P.optimized.family.problem.exec.derivedRequestIO.length ≤
      orderOf (alphaM P.honestTuple.1)) :
    alphaM P.honestTuple.1 ∉ OptimizedHostileTimestamps.TimestampCollisionEvent
      (P.hostileRequests (canonicalComputeTrace P)).length := by
  rw [hostileRequests_canonical_length H]
  exact OptimizedHostileTimestamps.not_mem_event_of_le_orderOf hα0 hord

/-! ## Component 4: the fields that hold -/

/-- On an accepted execution, `decompose` / `halt` rows carry the zero memory record. -/
theorem inactiveMem_of_accepted {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hacc : exec.MemoryRowsAccepted) (i : Fin cfg.memRows)
    (h1 : (exec.memoryPubAt i).st ≠ .read_root) (h2 : (exec.memoryPubAt i).st ≠ .verify_child) :
    (exec.memoryPubAt i).mem = ComputeTable.MemRec.zero := by
  have hrow := List.forall_iff_forall_mem.1 hacc _ (exec.memoryRowAt_mem i)
  obtain ⟨-, -, ⟨-, heq, -⟩, -⟩ := hrow
  unfold MemoryTable.eqBlk at heq
  change MemoryTable.eqBlk _ (exec.memoryPubAt i) at heq
  unfold MemoryTable.eqBlk at heq
  cases hst : (exec.memoryPubAt i).st with
  | decompose => rw [hst] at heq; exact heq.2.2.2
  | halt => rw [hst] at heq; exact heq.2.2.2.2.2.2
  | read_root => exact absurd hst h1
  | verify_child => exact absurd hst h2

/-- **`inactiveMem` at every buildable package.** -/
theorem inactiveMem_buildable (E : BuildableNockExecution F K) (I : Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    ∀ i : Fin (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.family.problem.cfg.memRows,
      ((buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.family.problem.exec.memoryPubAt i).st ≠ .read_root →
      ((buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.family.problem.exec.memoryPubAt i).st ≠ .verify_child →
      ((buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.family.problem.exec.memoryPubAt i).mem =
        ComputeTable.MemRec.zero :=
  fun i => inactiveMem_of_accepted E.exec (BuildablePackage.memoryRowsAccepted E) i

/-- **`interNe` at every package built from a pole chosen by `interPoleOfE`.** -/
theorem interNe_of_interPoleOfE (E : BuildableNockExecution F K) (I : Inputs E)
    (γ : K) (hcard : 2 * ((executionInterRecords E).requests.length +
        (executionInterRecords E).responses.length) + 1 < Fintype.card K)
    (hI : I.memoryExtensionFold = interPoleOfE E γ hcard)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges = (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled.interPole ≠ 0 := by
  show I.memoryExtensionFold ≠ 0
  rw [hI]
  exact interPoleOfE_ne_zero E γ hcard



open OptimizedCanonicalHostileLists OptimizedStrictPackage in
/-- **If the internal pole is `-γ^8` and some row is `halt` (zero record, `C' = 1`), the honest
pair IS in the all-row pole-hit event**, at any package.  So `interGamma8` cannot be dropped, and
the generator's pole choice (`interPoleOfE`, which avoids only the active records' hits and `0`)
does not supply it. -/
theorem honest_pair_hit_of_pole_neg_gamma8 (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : (P.optimized.family.problem.exec.memoryPubAt i).st = .halt)
    (hmem : (P.optimized.family.problem.exec.memoryPubAt i).mem = ComputeTable.MemRec.zero)
    (hc : (P.optimized.family.problem.exec.memoryPubAt i).cprime = 1)
    (hpole : P.optimized.sampled.interPole + P.optimized.sampled.sampled.coins.gamma ^ 8 = 0) :
    (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.interPole) ∈
      allRowPoleHitEvent (P.memorySourceEnv (honestMemoryTrace P))
        (P.memoryBaseEnv (honestMemoryTrace P)) := by
  simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv (honestMemoryTrace P) i)
      (P.memoryBaseEnv (honestMemoryTrace P) i), ?_, ?_⟩
  · simp only [List.append_nil]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · have hvrec := canonical_memRowRecord P i
    rw [hvrec, OptimizedMemorySemanticRealization.rowRecord10, RecordCarrier.rlc_withExp]
    simp only [OptimizedMemorySemanticRealization.reqIdxNat, hst]
    rw [hmem, hc, rlc_encRecC_memRec_zero]
    simpa using hpole

/-! ## Component 3 at the generated carrier: both premises are `hwin` -/

section Generated

open Nock.Walk
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen

variable {q Λ : ℕ}
    {z α : K} {hz : z ≠ 0} {htwo : (2 : K) ≠ 0} {a b c : K}
    {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
    {hmi : chal.memoryInputs = memInputs z}
    {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
    {hseed : SeedGood z t}
    {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
    {hΛ : 1 ≤ Λ} {hconf : TraceConfined Λ (airReorder t)}
    {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
    {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
    {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
    {B : ℕ} {hB : B ≤ orderOf α}
    {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
    {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
    {hKsz2 : 2 * (genExactConfig (F := F) chal Ksz orbit horb (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
    {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy q}
    {hq : 11 < q} {hchar : q = ringChar K}
    {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
      (genMemoryForest z α chal.lam (memInputs z) t))}
    {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
      (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
    {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
      (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
    {hKszChar : Ksz < ringChar K}
    {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
    {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤ 2 ^ orbit.h}
    {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K}


/-- At the generated carrier the timestamp base is the §1 binder `α`, nonzero and of order
above the honest record count, both from `hwin` (`programAcc + 3 < B ≤ orderOf α`). -/
theorem gen_timestamp_premises :
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.challenges.α ≠ 0 ∧
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤
      orderOf (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.challenges.α := by
  have hαeq : chal.α = α := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  have hlen := genExactExecution_derivedRequestIO_length (F := F) z α chal Ksz orbit horb a b c t
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem
  have hlt : accAt (airReorder t) (bfsRows (airReorder t)).length < orderOf α := by omega
  refine ⟨?_, ?_⟩
  · show chal.α ≠ 0
    rw [hαeq]
    exact alpha_ne_zero_of_lt_order hlt
  · show (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).derivedRequestIO.length ≤
      orderOf chal.α
    rw [hlen, hαeq]
    exact hlt.le

end Generated

end

end Nock.RedTeam.Batch957

#print axioms Nock.RedTeam.Batch957.timestamp_honest
#print axioms Nock.RedTeam.Batch957.inactiveMem_buildable
#print axioms Nock.RedTeam.Batch957.interNe_of_interPoleOfE
#print axioms Nock.RedTeam.Batch957.gen_timestamp_premises
#print axioms Nock.RedTeam.Batch957.honest_pair_hit_of_pole_neg_gamma8
