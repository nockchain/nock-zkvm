import Nock.RedTeam.Batch1250Thm54HonestGoodGenerated
import Nock.RedTeam.Batch1251Thm54HonestPairNotDiagonal

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1257Thm54HonestSeedWidenedChain.lean

The chain fixes the seed only at `p64` (`romSeedVcomp`); everything below is seed-generic and the
  package is built in `exists_package_of_carrier` as `Batch1061.genPkg` at the chain's values
  (`cwa = wg = compilerWalkCoin pOrbit`, `mef = 0`, `mwa = α`).  This module
  * `GoodSeed.exists_vcomp_seedX_allLambda`: the existing four seed conditions plus `z ∉ X`, under
    `seedBudgetVcomp Λ rows + |X| < |K|` (a new worker; `GenSeedVcomp` / `Gen.lean` untouched);
  * `nvX_p68` / `nvX_p69`: one new level on the seed-generic generator data, replaying the chain's own
    discharges, building `genPkg` explicitly and taking the statement from
    `statement_of_generated_residual`; the budget from `Batch1251.seedBudgetPairB_lt_pow`;
  * `nvX_zmod`: `nockCompiles_zmod`'s binders verbatim plus `X`, `|X| ≤ M·(2(M ⊔ Λ) − 1)` and a predicate
    `Q` proved at every generated package whose seed avoids `X`; conclusion `∃ package, Stmt ∧ claim ∧
    lam ∧ Q package ∧ nprSeed package.honestTuple.1 ∉ X`.  `hp : 25 ≤ p` is unmoved.
  * `demo_alphaNe_zmod`: plumbing positive control (`X = ∅`, `Q := alphaM ≠ 0`).

  -- the paper
-/


set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.SizeWindowCounting
open ComputeTable

variable {K : Type} [Field K]

namespace GoodSeed

variable [Fintype K] [DecidableEq K]

/-- **Stage 2: the joint seed, widened by an extra `z`-free bad set `X`.**  `exists_vcomp_seed_of_accepted`
with `X` added to the union; budget `seedBudgetVcomp Λ rows + |X|`. -/
theorem exists_vcomp_seedX_of_accepted {lmb : K} {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (X : Finset K)
    (hcard : seedBudgetVcomp Λ (bfsForest [bfsAssign (airReorder t)]).length + X.card
        < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
              (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder t))
                (genMemoryForest z α lmb (memInputs z) t))
      ∧ SeedGood z t ∧ z ∉ X := by
  classical
  let rows := (bfsForest [bfsAssign (airReorder t)]).length
  let Cempty := genSkeletonP8Census (K := K) hΛ h hconf
    ([] : List (NTree (GenMemoryRow K)))
  let Sempty := genSemanticSkeleton (bfsAssign (airReorder t))
    ([] : List (NTree (GenMemoryRow K)))
  let KM : Finset K :=
    (({0} : Finset K) ∪ Cempty.census.badSeeds (K := K)) ∪
      sizeWindowFailureSeeds (K := K) Sempty
  let D : Finset K :=
    Finset.univ.filter (fun z : K => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g)
  have hrows : (bfsRows (airReorder t)).length = rows := by
    unfold rows
    rw [bfsRows_length, bfsForest_bfsAssign_length]
  have hKMcard : KM.card ≤ seedBudget Λ rows := by
    have h1 : (({0} : Finset K) ∪ Cempty.census.badSeeds (K := K)).card
        ≤ 1 + (3 + 10 * (computeSkeletonRows Sempty).length) * (2 * Λ - 1) := by
      refine (Finset.card_union_le _ _).trans ?_
      have hcen := (Cempty.census.badSeeds_card_le (K := K)).trans
        (Nat.mul_le_mul_right (2 * Λ - 1) Cempty.count_le)
      simpa using Nat.add_le_add_left hcen 1
    have hlen : (computeSkeletonRows Sempty).length = rows := by
      unfold rows
      rw [computeSkeletonRows_length]
    rw [hlen] at h1
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add h1 (sizeWindowFailureSeeds_card_le Sempty Λ hwin)
  have hDcard : D.card ≤ rows * (3 * (2 * Λ - 1)) := by
    have := seedBad_card_le_of_generated hq hle hs hf hG h hΛ hconf
    rwa [hrows] at this
  have hunion : ((KM ∪ D) ∪ X).card < Fintype.card K := by
    refine lt_of_le_of_lt ?_ hcard
    refine (Finset.card_union_le _ X).trans ?_
    refine Nat.add_le_add_right ((Finset.card_union_le KM D).trans ?_) _
    have : rows * (3 * (2 * Λ - 1)) = 3 * rows * (2 * Λ - 1) := by
      ring
    rw [this] at hDcard
    exact Nat.add_le_add hKMcard hDcard
  obtain ⟨z, hz⟩ := exists_notMem_of_card_lt hunion
  have hzX : z ∉ X := fun h => hz (Finset.mem_union_right _ h)
  have hzKM : z ∉ KM := fun h => hz (Finset.mem_union_left _ (Finset.mem_union_left D h))
  have hzD : z ∉ D := fun h => hz (Finset.mem_union_left _ (Finset.mem_union_right KM h))
  have hz01 : z ∉ ({0} : Finset K) ∪ Cempty.census.badSeeds (K := K) :=
    fun h => hzKM (Finset.mem_union_left _ h)
  have hzWin : z ∉ sizeWindowFailureSeeds (K := K) Sempty :=
    fun h => hzKM (Finset.mem_union_right _ h)
  have hz0 : z ≠ 0 :=
    fun h => hz01 (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have hzbad : z ∉ Cempty.census.badSeeds (K := K) :=
    fun h => hz01 (Finset.mem_union_right _ h)
  refine ⟨z, hz0, ?_, ?_, ?_, hzX⟩
  · rw [badSeeds_memoryForest_irrelevant
      (genSkeletonP8Census (K := K) hΛ h hconf (genMemoryForest z α lmb (memInputs z) t))
      Cempty]
    exact hzbad
  · rw [sizeWindowFailureSeeds_memoryForest_irrelevant (bfsAssign (airReorder t))
      (genMemoryForest z α lmb (memInputs z) t) ([] : List (NTree (GenMemoryRow K)))]
    exact hzWin
  · exact seedGood_raw_of_airReorder
      (seedGood_airReorder_of_not_mem z t hzD)

/-- The widened seed at every Form R `λ` (the census and windows read only the compute tree). -/
theorem exists_vcomp_seedX_allLambda {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (X : Finset K)
    (hcard : seedBudgetVcomp Λ (bfsForest [bfsAssign (airReorder t)]).length + X.card
        < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ (∀ lmb' : K, z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
              (genMemoryForest z α lmb' (memInputs z) t)).census.badSeeds)
      ∧ (∀ lmb' : K, z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder t))
                (genMemoryForest z α lmb' (memInputs z) t)))
      ∧ SeedGood z t ∧ z ∉ X := by
  obtain ⟨z, h0, hb, hw, hg, hx⟩ :=
    exists_vcomp_seedX_of_accepted (lmb := (0 : K)) hq hle hs hf hG h hΛ hconf α hwin X hcard
  refine ⟨z, h0, fun lmb' => ?_, fun lmb' => ?_, hg, hx⟩
  · rw [badSeeds_memoryForest_irrelevant _
      (genSkeletonP8Census (K := K) hΛ h hconf (genMemoryForest z α (0 : K) (memInputs z) t))]
    exact hb
  · rw [sizeWindowFailureSeeds_memoryForest_irrelevant _ _
      (genMemoryForest z α (0 : K) (memInputs z) t)]
    exact hw

end GoodSeed

end Nock.NockVMROM.Thm54.TraceGen


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1257

open scoped Polynomial
open Polynomial
open Nock Nock.Walk Nock.Framework
open Nock.Framework.Thm54
open Module
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.RedTeam.Batch1061 (genPkg gen_honest_accepted)

open Nock.NockVMROM.Thm54.TraceGen.GoodSeed

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
section Generated

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





set_option quotPrecheck false in
set_option hygiene false in
local notation "GP" => genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
  hinterCard hhon hprl hmore hord hordM hrows

set_option quotPrecheck false in
set_option hygiene false in
local notation "EG" => genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
  hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
  haxis hbad hout hKszChar hprogCap hmemCap hfirst

set_option quotPrecheck false in
set_option hygiene false in
local notation "IG" => inputsOfCarrier (EG) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
  hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon


theorem genPkg_statement
    (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3) {hOrb : ℕ}
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (hax : FormRAxisBound (GP).optimized.sampled (GP).optimized.basis)
    (hbasis : FormRBasis (GP).optimized.basis) (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (GP)
      ∧ (GP).optimized.verifier.raw.claim = ⟨subject, formula, result⟩
      ∧ (GP).optimized.objects.cfg.challenges.lam = chal.lam := by
  refine ⟨statement_of_generated_residual _ _ _ hprl hmore hord hordM hrows
    (genDataOfProgram_claimGeneratedD hG) hF hax hbasis hwidth,
    ?_, rfl⟩
  exact (commitmentResidualOfZero _).claim_eq.symm.trans
    (genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
      orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
      hbad hout hKszChar hprogCap hmemCap hfirst)


set_option maxHeartbeats 16000000 in
/-- **Stage 3 (the assembly route).**  `nockCompiles_p68`'s shape with the seed chosen by
`exists_vcomp_seedX_allLambda` (the four live seed conditions AND `z ∉ X`), budget widened by `|X|`,
and the package EXPOSED: any predicate `Q` that holds at every generated package `genPkg` whose seed
avoids `X` holds at the package produced. -/
theorem nvX_p68 {hOrb : ℕ} (lmb : K) (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject) (hf : FieldEmbedding.BoundedBy q formula)
    (hΛL : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (X : Finset K)
    (hseedX : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        + X.card < Fintype.card K)
    (hp64 : ringChar F < 2 ^ 64)
    (hOrbPos : 1 ≤ hOrb)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1)
    (hFprime : GeneratedField.PrimeFieldElems F)
    (hcompR : (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
      ≤ 2 ^ hOrb)
    (hmemR : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ hOrb)
    (hwinA : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf α)
    (hKszChar0 : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hprogCapA : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ hOrb)
    (hmemCapA : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 1 ≤ 2 ^ hOrb)
    (hrowsA : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
        < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (Q : OptimizedFullStrictNockVMROMPackage F K hOrb → Prop)
    (hQ : ∀ {z : K} {hz : z ≠ 0} {a b c : K}
      {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
      {hmi : chal.memoryInputs = memInputs z}
      {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
      {t : NTree (GenComputeRow K)}
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
      {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
      {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
        (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
      {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder t))
          (genMemoryForest z α chal.lam (memInputs z) t))}
      {hKszChar : Ksz < ringChar K}
      {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
      {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤
        2 ^ orbit.h}
      {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K},
    ∀ (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3)
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hFp : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64),
      z ∉ X → Q (GP)) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ Q package
        ∧ nprSeed package.honestTuple.1 ∉ X := by
  have hrom := evalGRom_le_evalRom hgrom
  have hG := evalGRom_le_evalGBy hgrom
  have h : genComputeSkeleton (K := K) fuel subject formula =
      .ok (romTree (K := K) (evalGRom_le_evalRom hgrom), result) := romTree_spec (K := K) _
  have hconf : TraceConfined Λ (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) :=
    traceConfined_of_leafBound hΛL
  have hΛ : 1 ≤ Λ := one_le_of_hΛ_conf hconf
  have hwinN := sizeWindowNounsBoundedBy_of_traceConfined hΛ h hconf
    ([] : List (NTree (GenMemoryRow K)))
  obtain ⟨z, hz, hbadA, houtA, hseed, hzX⟩ :=
    GoodSeed.exists_vcomp_seedX_allLambda (by omega : 1 < q) (le_of_eq hchar) hs hf hG h hΛ
      hconf α hwinN X hseedX
  have hrowsCard : (bfsForest [airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
      < Fintype.card K :=
    airReorder_rows_lt_card_of_seedBudgetVcomp hΛ _ (by omega)
  obtain ⟨a, b, c, hcoins⟩ := exists_computeCoinsGeneric_airReorder z α _ hrowsCard
  have hcomp : (bfsForest [genComputeRows z α (romTree (K := K) (evalGRom_le_evalRom hgrom))]).length
      ≤ 2 ^ (compilerExecutionOrbit (F := F) (K := K) hOrb hOrbPos hF).h := by
    rw [genComputeRows_bfsForest_length]; exact hcompR
  have hmem : (bfsForest (genMemoryForest z α (compilerChallengeVector α z a b c lmb).lam
      (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
      ≤ 2 ^ (compilerExecutionOrbit (F := F) (K := K) hOrb hOrbPos hF).h := by
    change programMemRowsL lmb z α _ ≤ 2 ^ hOrb
    rw [← programMemShape_spec z α _]; exact hmemR
  have hmemCap : (bfsForest (genMemoryForest z α (compilerChallengeVector α z a b c lmb).lam
      (memInputs z) (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length + 1
      ≤ 2 ^ (compilerExecutionOrbit (F := F) (K := K) hOrb hOrbPos hF).h := by
    change programMemRowsL lmb z α _ + 1 ≤ 2 ^ hOrb
    rw [← programMemShape_spec z α _]; exact hmemCapA
  have hmempos := genComputeSkeleton_hmempos (lmb := lmb) z α (memInputs z) h
  have hKszChar : compilerKszOfL lmb z α (romTree (K := K) (evalGRom_le_evalRom hgrom)) <
      ringChar K := by
    rw [compilerKszOfL_irrel lmb z (0 : K) α _, ← compilerKszOf_eq_L]; exact hKszChar0
  have hfirst : ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))))
      n → ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K := by
    intro n hn r hr
    rw [← hchar]
    exact romTree_assigned_request_axes_lt (q := q) (by omega) hgrom hs hf n hn r hr
  have hcard : RecordCarrier.honestIOBound
      (compilerNOfL lmb z α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (compilerNOfL lmb z α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (Fintype.card K) < Fintype.card (K × K) := by
    rw [compilerNOfL_irrel lmb z (0 : K) α _]
    exact hcard_of_hF_hK (F := F) (K := K) hOrbPos hK hF _
      (by rw [← compilerNOf_eq_L]; exact compilerNOf_le_two_pow hmemR hprogCapA)
  have hbad := hbadA lmb
  have hout := houtA lmb
  let P := Nock.RedTeam.Batch1061.genPkg (F := F) (K := K) (q := q) (Λ := Λ) (z := z) (α := α)
      (hz := hz) (htwo := htwo) (a := a) (b := b) (c := c)
      (chal := compilerChallengeVector α z a b c lmb) (hinp := rfl) (hmi := rfl)
      (Ksz := compilerKszOfL lmb z α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (orbit := compilerExecutionOrbit (F := F) (K := K) hOrb hOrbPos hF) (horb := hOrbPos)
      (h := h) (hF := hFprime) (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ) (hconf := hconf)
      (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := orderOf α) (hB := le_rfl)
      (hwin := hwinA) (hKsz := compilerKsz_acc _ _)
      (hKsz2 := by
        change 2 * programMemRootsL lmb z α _ ≤
          compilerKsz (programAcc _) (programMemRootsL lmb z α _)
        exact compilerKsz_two_mul _ _)
      (hb := genComputeSkeleton_skeletonBounded z α (memInputs z) (by omega) hs hf hG h)
      (hq := hq) (hchar := hchar)
      (haxis := genComputeSkeleton_axisRange (by omega) hs hf hG h _)
      (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCapA)
      (hmemCap := hmemCap) (hfirst := hfirst)
      (compilerStateTagChar hq hchar) hK (compilerPackageOrbit (F := F) hOrb hOrbPos hF) le_rfl
      (compilerNOfL lmb z α (romTree (K := K) (evalGRom_le_evalRom hgrom)))
      (genExactExecution_requestIO_le (F := F) z α _ _ _ _ a b c _ _ hmempos hcomp hmem _
        (compilerN_acc _ _))
      (genExactExecution_responseIO_le (F := F) _ _ _ _ a b c _ _ hmempos hcomp hmem _
        (compilerN_mem _ _))
      hcard (compilerWalkCoin (F := F) (K := K) (compilerPackageOrbit (F := F) hOrb hOrbPos hF))
      (compilerWalkCoin (F := F) (K := K) (compilerPackageOrbit (F := F) hOrb hOrbPos hF)) 0
      (interCard_of_unionBound _ (compilerN_mem _ _) hcard)
      (genBuildableOfProgram_honestVer (F := F) (q := q) (Λ := Λ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (genBuildableOfProgram_pairedRecordLayout (F := F) (q := q) (Λ := Λ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      genBuildableOfProgram_laterSeedZeros
      (fun hge => compilerWalkOrder_of_le _ hcomp hge)
      (fun _ => memRowsL_le_orderOf_of_shape hmemOrd)
      (genBuildableOfProgram_rowsBound_of_program hrowsA)
  have hbasis : FormRBasis P.optimized.basis := compilerBasis_formR (F := F) (K := K) hK
  have hwidth : FormRWidth F := GenFormRAxisLambda.FormRWidth_of_hp64
    (by rw [Algebra.ringChar_eq F K, ← hchar]; omega) hp64
  have hax : FormRAxisBound P.optimized.sampled P.optimized.basis :=
    (GenFormRAxisLambda.buildFullPackage_formRAxisBound_iff _ _ _ _ _ _ _ _ _).mpr (by
      erw [GenFormRAxisLambda.genBuildableOfProgram_exec_computeRows]
      exact GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound (q := q) (by omega) hs hf
        (evalGRom_le_evalGBy hgrom) (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
        (hchar.trans (Algebra.ringChar_eq F K).symm)
        (by rw [hchar, ← Algebra.ringChar_eq F K]; exact hp64)
        (compilerBasis_formR (F := F) (K := K) hK) _ α a b c)
  have hS : OptimizedFullStrictThm54Statement P
      ∧ P.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
      ∧ P.optimized.objects.cfg.challenges.lam = (compilerChallengeVector α z a b c lmb).lam :=
    genPkg_statement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hFprime hax hbasis hwidth
  have hQP : Q P := hQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hFprime hs hf hG hp64 hzX
  exact ⟨P, hS.1, hS.2.1, hS.2.2, hQP, hzX⟩


/-- **Stage 3b (budget from the §1 bounds).**  `nvX_p68` with the widened budget derived from
`rows, Λ < p`, `3M ≤ p − 1`, `25 ≤ p` (`Batch1251.seedBudgetPairB_lt_pow`, `hp` UNMOVED) whenever
`|X| ≤ M·(2(M ⊔ Λ) − 1)` (`M = programMemShape α t`), and the four capacities from one `programFit`
bound. -/
theorem nvX_p69 {hOrb : ℕ} (lmb : K) (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject) (hf : FieldEmbedding.BoundedBy q formula)
    (hΛL : programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom))) ≤ Λ)
    (hΛp : Λ < ringChar K)
    (X : Finset K)
    (hX : X.card ≤ programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) *
      (2 * (programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ⊔ Λ) - 1))
    (hp25 : 25 ≤ ringChar K)
    (hM3 : 3 * programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ ringChar K - 1)
    (hp64 : ringChar F < 2 ^ 64)
    (hOrbPos : 1 ≤ hOrb)
    (hK : Module.finrank F K = 3)
    (hF : 3 * 2 ^ hOrb ∣ Fintype.card F - 1)
    (hFprime : GeneratedField.PrimeFieldElems F)
    (hfit : programFit α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ 2 ^ hOrb)
    (hwinA : programAcc (romTree (K := K) (evalGRom_le_evalRom hgrom)) + 3 < orderOf α)
    (hmemOrd : programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) ≤ orderOf α)
    (hKszChar0 : compilerKszOf (0 : K) α
      (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (hrowsA : 3 * (bfsRows (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))).length
        < ringChar K ∧
      programMemShape α (romTree (K := K) (evalGRom_le_evalRom hgrom)) < ringChar K)
    (Q : OptimizedFullStrictNockVMROMPackage F K hOrb → Prop)
    (hQ : ∀ {z : K} {hz : z ≠ 0} {a b c : K}
      {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
      {hmi : chal.memoryInputs = memInputs z}
      {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
      {t : NTree (GenComputeRow K)}
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
      {haxis : SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
      {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
        (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
      {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder t))
          (genMemoryForest z α chal.lam (memInputs z) t))}
      {hKszChar : Ksz < ringChar K}
      {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
      {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤
        2 ^ orbit.h}
      {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K},
    ∀ (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank F K = 3)
    (pOrbit : StrictOrbitDomain F 3 hOrb)
    (hcap : 2 ^ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ hOrb)
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hFp : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64),
      z ∉ X → Q (GP)) :
    ∃ package : OptimizedFullStrictNockVMROMPackage F K hOrb,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ Q package
        ∧ nprSeed package.honestTuple.1 ∉ X := by
  have hrowsLt := seedRows_lt_char_of_hKszChar α _ hKszChar0
  have hb := Nock.RedTeam.Batch1251.seedBudgetPairB_lt_pow hrowsLt hΛp hM3 hp25
  have hcube := card_K_ge_char_cubed (F := F) (K := K) hK
  have hseedX : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))]).length
        + X.card < Fintype.card K := by
    unfold Nock.RedTeam.Batch1251.seedBudgetPairB at hb
    omega
  exact nvX_p68 (htwo := htwo) (hq := hq) (hchar := hchar) lmb hgrom hs hf hΛL X hseedX hp64
    hOrbPos hK hF hFprime ((programCompRows_le_fit α _).trans hfit) ((programMemShape_le_fit α _).trans hfit)
    hwinA hmemOrd hKszChar0 ((programAcc_succ_le_fit α _).trans hfit)
    ((programMemShape_succ_le_fit α _).trans hfit) hrowsA Q hQ

end Generated


section Zmod

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional (ZMod p) K]

set_option quotPrecheck false in
set_option hygiene false in
local notation "GP" => genPkg (F := ZMod p) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
  hinterCard hhon hprl hmore hord hordM hrows

/-- **Stage 3c (§1 spelling).**  `nockCompiles_zmod`'s binders verbatim, plus the extra `z`-free bad set
`X` with `|X| ≤ M·(2(M ⊔ Λ) − 1)` and a predicate `Q` that holds at every generated package whose seed
avoids `X`.  No new arithmetic side condition: `hp : 25 ≤ p` is unmoved. -/
theorem nvX_zmod
    (α lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ∣ p - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)
    (hKszChar : compilerKszOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p)
    (X : Finset K)
    (hX : X.card ≤ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) * (2 * (programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ⊔ (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) - 1))
    (Q : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) → Prop)
    (hQ : ∀ {hq : 11 < p} {hchar : p = ringChar K} {htwo : (2 : K) ≠ 0} {z : K} {hz : z ≠ 0} {a b c : K}
      {chal : ChallengeVector K} {hinp : chal.computeInputs = ⟨α, z, a, b, c⟩}
      {hmi : chal.memoryInputs = memInputs z}
      {Ksz : ℕ} {orbit : OrbitDomain K} {horb : 1 ≤ orbit.h}
      {t : NTree (GenComputeRow K)}
      {h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)}
      {hseed : SeedGood z t}
      {hcoins : ComputeCoinsGeneric z α a b c (airReorder t)}
      {hΛ : 1 ≤ (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))} {hconf : TraceConfined (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) (airReorder t)}
      {hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length}
      {hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h}
      {hmem : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length ≤ 2 ^ orbit.h}
      {B : ℕ} {hB : B ≤ orderOf α}
      {hwin : accAt (airReorder t) (bfsRows (airReorder t)).length + 3 < B}
      {hKsz : accAt (airReorder t) (bfsRows (airReorder t)).length ≤ Ksz}
      {hKsz2 : 2 * (genExactConfig (F := ZMod p) chal Ksz orbit horb (genComputeRows z α t)
        (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).kMem ≤ Ksz}
      {hb : (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t)).BoundedBy p}
      {haxis : SkeletonAxisRange p (genSemanticSkeleton (bfsAssign (airReorder t))
        (genMemoryForest z α chal.lam (memInputs z) t))}
      {hbad : z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
        (genMemoryForest z α chal.lam (memInputs z) t)).census.badSeeds}
      {hout : z ∉ SizeWindowCounting.sizeWindowFailureSeeds (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder t))
          (genMemoryForest z α chal.lam (memInputs z) t))}
      {hKszChar : Ksz < ringChar K}
      {hprogCap : accAt (airReorder t) (bfsRows (airReorder t)).length + 1 ≤ 2 ^ orbit.h}
      {hmemCap : (bfsForest (genMemoryForest z α chal.lam (memInputs z) t)).length + 1 ≤
        2 ^ orbit.h}
      {hfirst : ∀ n, InTree (bfsAssign (airReorder t)) n →
        ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar K},
    ∀ (stc : NodeEncoding.StateTagChar K) (hK : Module.finrank (ZMod p) K = 3)
    (pOrbit : StrictOrbitDomain (ZMod p) 3 (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))))
    (hcap : 2 ^ (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.orbit.h ≤ 2 ^ (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))))
    (n : ℕ)
    (hreq : (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedRequestIO.length ≤ n)
    (hresp : (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst).exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa wg : K) (mef : K)
    (hinterCard : 4 * (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z
        α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (hord : 2 ≤ (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows → (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := ZMod p) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := ZMod p) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := ZMod p) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hFp : GeneratedField.PrimeFieldElems (ZMod p))
    (hsB : FieldEmbedding.BoundedBy p subject) (hfB : FieldEmbedding.BoundedBy p formula)
    (hG : FieldEmbedding.evalGBy p fuel subject formula = some result)
    (hp64 : ringChar (ZMod p) < 2 ^ 64),
      z ∉ X → Q (GP)) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ Q package
        ∧ nprSeed package.honestTuple.1 ∉ X := by
  have hr : ringChar K = p := ringChar_eq_prime (p := p) (K := K)
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq : 11 < p := by omega
  have hchar : p = ringChar K := hr.symm
  have hM : programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) :=
    (programMemShape_le_fit α _).trans (le_two_pow_orbitHeight _)
  have hM3 := Nock.RedTeam.Batch1251.threeM_le_of_hF hp2 hF hM
  have hrows := hrows_of_hF (p := p) (K := K) α _ hF
  exact nvX_p69 (F := ZMod p) (K := K) (q := p) (Λ := (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))))) (hq := hq) (hchar := hchar)
    (htwo := two_ne_zero_of_hq (K := K) hq hchar) lmb (evalGRom_of_runBounded hrun hbound) hs hf
    le_rfl (by rw [hr]; exact hΛp) X hX (by rw [hr]; exact hp) (by rw [hr]; exact hM3)
    (by rw [ZMod.ringChar_zmod_n]; exact hp64) (orbitHeight_pos _) hK
    (by simpa [ZMod.card] using hF) (GeneratedField.primeFieldElems_zmod p) (le_two_pow_orbitHeight _) hwin.1 hwin.2
    (by rw [hr]; exact hKszChar) (by rw [hr]; exact hrows) Q
    (hQ (hq := hq) (hchar := hchar) (htwo := two_ne_zero_of_hq (K := K) hq hchar))



theorem demo_alphaNe_zmod
    (α lmb : K)
    {fuel : ℕ} {subject formula : Noun}
    {result : Noun}
    (hrun : Nock.evalN fuel subject formula = some result)
    (hbound : RunBoundedBy p fuel subject formula)
    (hs : FieldEmbedding.BoundedBy p subject)
    (hf : FieldEmbedding.BoundedBy p formula)
    (hΛp : (programLeafBound (airReorder (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))) < p)
    (hp : 25 ≤ p)
    (hp64 : p < 2 ^ 64)
    (hK : Module.finrank (ZMod p) K = 3)
    (hF : 3 * 2 ^ orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)))) ∣ p - 1)
    (hwin : programAcc (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) + 3 < orderOf α ∧ programMemShape α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) ≤ orderOf α)
    (hKszChar : compilerKszOf (0 : K) α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))) < p) :
    ∃ package : OptimizedFullStrictNockVMROMPackage (ZMod p) K (orbitHeight (programFit α (romTree (K := K) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound))))),
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subject, formula, result⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb
        ∧ alphaM package.honestTuple.1 ≠ 0 := by
  obtain ⟨P, h1, h2, h3, h4, -⟩ := nvX_zmod α lmb hrun hbound hs hf hΛp hp hp64 hK hF hwin hKszChar
    ∅ (by simp) (fun P => alphaM P.honestTuple.1 ≠ 0)
    (fun stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM
        hrows hFp hsB hfB hG hp64 _ =>
      Nock.RedTeam.Batch1250.alphaNe_genPkg stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
        hinterCard hhon hprl hmore hord hordM hrows hFp hsB hfB hG hp64)
  exact ⟨P, h1, h2, h3, h4⟩

end Zmod

end

end Nock.RedTeam.Batch1257

#print axioms Nock.RedTeam.Batch1257.nvX_p68
#print axioms Nock.RedTeam.Batch1257.nvX_p69
#print axioms Nock.RedTeam.Batch1257.nvX_zmod
#print axioms Nock.RedTeam.Batch1257.demo_alphaNe_zmod
