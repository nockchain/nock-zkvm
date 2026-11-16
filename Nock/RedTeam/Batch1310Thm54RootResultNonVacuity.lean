import Nock.RedTeam.Batch1258Thm54HonestNonVacuity
import Nock.NockVMROM.Thm54.P8Core.RootResultBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1310Thm54RootResultNonVacuity.lean

  * `HoldsPremises P c Qc Qm`: the full premise list of `holds_of_traces` (= `Batch1173`'s), bundled.
  * `holds_of_premises`: the premises give the guarded and the Nock evaluation at the claimed result.
  * `nonvacuous_generated_holds` (general `F`, generated package `genPkg`, honest tuple, honest traces):
    every premise discharged, as in `Batch1258.nonvacuous_generated` (binders verbatim: the generator's,
    the z-free seed condition `hzp`, and `hF`).
  * `nonvacuous_zmod_holds` (section-1 spelling): `nockCompiles_zmod`'s binders VERBATIM, conclusion
    `∃ package, Stmt ∧ claim ∧ lam ∧ HoldsAt package`, no open premise.
  * `nonvacuous_zmod_semantic`: the same package, with `holds_of_traces`'s conclusion fired.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Nock.RedTeam.Batch1310

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

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-- **The premise list of `holds_of_traces`** (`Batch1173`'s), at `(P, c, Qc, Qm)`. -/
def HoldsPremises {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) : Prop :=
  DeployedAcceptanceAt P c Qc Qm ∧
    c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm) ∧
    c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) ∧
    FormRAxisBound P.optimized.sampled P.optimized.basis ∧
    FormRBasis P.optimized.basis ∧
    FormRWidth F ∧
    StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c ∧
    (∃ (gfuel : ℕ) (G : NTree (GenComputeRow K)) (R : Noun),
      genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = .ok (G, R) ∧
      programLeafBound (airReorder G) ≤ P.optimized.Λ) ∧
    (∃ (fuel : ℕ) (r : Noun), FieldEmbedding.evalGBy (ringChar K) fuel
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula = some r) ∧
    FieldEmbedding.BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject ∧
    FieldEmbedding.BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula ∧
    (∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)

/-- `HoldsPremises` at `P`'s honest tuple and honest traces. -/
def HoldsAt {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) : Prop :=
  HoldsPremises P P.honestTuple (QcH P) (QmH P)

/-- **The semantic `p8` from the bundled premises.** -/
theorem holds_of_premises {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (H : HoldsPremises P c Qc Qm) :
    ∃ fuel, FieldEmbedding.evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result := by
  obtain ⟨hacc, hgood, hgoodEv, hax, hbasis, hwidth, h, ⟨gfuel, G, R, hgen, hΛG⟩, ⟨fuel, r, hG⟩,
    bs, bf, hF⟩ := H
  exact ⟨fuel, RootResultBridge.holds_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG
    bs bf hΛG hF⟩

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

/-- **Non-vacuity of the semantic `p8` at the generated package** (honest tuple, honest traces): every
premise of `holds_of_traces` discharged; binders = `Batch1258.nonvacuous_generated`'s. -/
theorem nonvacuous_generated_holds
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
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hzp : z ∉ PreSeedCensus.pairBadSeeds (K := K)
      ((Nock.RedTeam.Batch1253.AtGen.rows0 t).length ⊔ Λ) (Nock.RedTeam.Batch1253.AtGen.honestPairs0 F K q t))
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    HoldsAt (GP) := by
  have hpair := Nock.RedTeam.Batch1253.AtGen.hpair_of_seed (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hG hF hzp
  have hgood := Nock.RedTeam.Batch1250.hgood_genPkg_of_pair (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hpair
  have htopo := Nock.RedTeam.Batch1254.T5.htopo_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hgood
  have haxisEv := Nock.RedTeam.Batch1254.T5.haxisEv_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64 hgood
  have hSc := Nock.RedTeam.Batch1255.Gen.builtComputeTree_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hp8Ev := Nock.RedTeam.Batch1255.Consumers.hp8Ev_of_computeTree_eq (GP) _ _ (GP).honestTuple hgood hSc htopo haxisEv
  have hpairEv := Nock.RedTeam.Batch1255.Consumers.hpairEv_of_computeTree_eq (GP) _ _ (GP).honestTuple hgood hSc
  have hrootEv := Nock.RedTeam.Batch1255.Consumers.hrootEv_of_computeTree_eq (GP) _ _ (GP).honestTuple hSc
  -- as in `Batch1250.nonvacuous_generated_of_open`
  have G := Nock.RedTeam.Batch993.hgoodFill_generated (F := F) (K := K) stc hK pOrbit hcap n hreq
    hresp hcard cwa α wg (fun _ => 0) mef hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hacc := gen_honest_accepted (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
    hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hα := Nock.RedTeam.Batch1250.alphaNe_genPkg (F := F) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
    hinterCard hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64
  have hgoodEv := Nock.RedTeam.Batch1250.hgoodEv_of_pinned (GP) _ _ (GP).honestTuple hgood hp8Ev hpairEv hrootEv hα
  have hbasis : FormRBasis (GP).optimized.basis := compilerBasis_formR (F := F) (K := K) hK
  have hgood' : (GP).honestTuple ∉ (GP).optimizedFailureEvent (canonicalComputeTrace (GP))
      (canonicalMemoryTrace (GP)) := by
    rw [← honestQc_QcH (GP), ← honestQm_QmH (GP)]; exact hgood
  have hW0 := Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed (GP) (GP).honestTuple
    (canonicalComputeTrace (GP)) (canonicalMemoryTrace (GP)) hacc.compute_satisfies
    hacc.memory_satisfies
    (Nock.RedTeam.Batch824.memStateTagChar_of_package (GP)) G.hax hbasis
    G.hwidth hacc hgood'
  have hW : StrategyOfTracesLift.TracesWalkHyps (GP).optimized
      (honestQc (GP) (GP).honestTuple (QcH (GP))) (honestQm (GP) (GP).honestTuple (QmH (GP)))
      (GP).honestTuple := by
    rw [honestQc_QcH (GP), honestQm_QmH (GP)]
    exact (Nock.RedTeam.Batch940.tracesWalkHyps_iff (GP) (GP).honestTuple _ _).2 hW0
  have hclaim : (GP).optimized.verifier.raw.claim = ⟨subject, formula, result⟩ :=
    genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
      orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
      hbad hout hKszChar hprogCap hmemCap hfirst
  have hgen : genComputeSkeleton (K := K) fuel (GP).optimized.verifier.raw.claim.subject
      (GP).optimized.verifier.raw.claim.formula = .ok (t, result) := by
    rw [hclaim]; exact h
  have hG' : FieldEmbedding.evalGBy (ringChar K) fuel (GP).optimized.verifier.raw.claim.subject
      (GP).optimized.verifier.raw.claim.formula = some result := by
    rw [hclaim, ← hchar]; exact hG
  have bs : FieldEmbedding.BoundedBy (ringChar K) (GP).optimized.verifier.raw.claim.subject := by
    rw [hclaim, ← hchar]; exact hsB
  have bf : FieldEmbedding.BoundedBy (ringChar K) (GP).optimized.verifier.raw.claim.formula := by
    rw [hclaim, ← hchar]; exact hfB
  have hΛG : programLeafBound (airReorder t) ≤ (GP).optimized.Λ :=
    leafBound_of_traceConfined hconf
  exact ⟨hacc, hgood, hgoodEv, G.hax, hbasis, G.hwidth, hW, ⟨fuel, t, result, hgen, hΛG⟩,
    ⟨fuel, result, hG'⟩, bs, bf, hF⟩

end Generated

section Zmod

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional (ZMod p) K]

open Nock.NockVMROM.Thm54.TraceGen.GoodSeed in
/-- The package is the chain's `genPkg` at the widened seed (`Batch1257.nvX_zmod`)
whose `z` also avoids the z-free pair bad set `Batch1253.Seed.pairBad` of the program; at it the
premises of the semantic `p8` hold at the honest tuple and honest traces (`HoldsAt`). -/
theorem nonvacuous_zmod_holds
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
        ∧ HoldsAt package := by
  have hrom := evalGRom_le_evalRom (evalGRom_of_runBounded hrun hbound)
  have hlen : (Nock.RedTeam.Batch1253.AtGen.rows0 (romTree (K := K) hrom)).length =
      programMemShape α (romTree (K := K) hrom) := by
    have e := congrArg List.length
      (Nock.RedTeam.Batch1253.genMemoryForest_bfs_sig (K := K) 0 α 0 (memInputs 0) (romTree (K := K) hrom))
    simp only [List.length_map] at e
    simpa [Nock.RedTeam.Batch1253.AtGen.rows0, Nock.RedTeam.Batch1253.AtGen.refForest,
      programMemShape, programMemRows, programMemRowsL] using e.symm
  have hX := Nock.RedTeam.Batch1253.Seed.pairBad_card_le (K := K) (ZMod p) p
    (programLeafBound (airReorder (romTree (K := K) hrom))) (romTree (K := K) hrom)
  rw [hlen] at hX
  obtain ⟨P, h1, h2, h3, h4, -⟩ := Nock.RedTeam.Batch1257.nvX_zmod α lmb hrun hbound hs hf hΛp hp hp64 hK hF
    hwin hKszChar
    (Nock.RedTeam.Batch1253.Seed.pairBad (K := K) (ZMod p) p
      (programLeafBound (airReorder (romTree (K := K) hrom))) (romTree (K := K) hrom)) hX HoldsAt
    (by
      intro hq hchar htwo z hz a b c chal hinp hmi Ksz orbit horb t h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb haxis hbad hout hKszChar hprogCap hmemCap hfirst
        stc hK pOrbit hcap n hreq hresp hcard cwa wg mef hinterCard hhon hprl hmore hord hordM hrows
        _hFp hsB hfB hG hp64 hzX
      have ht : t = romTree (K := K) hrom := by
        have e := h.symm.trans (romTree_spec (K := K) hrom)
        injection e with e'
        exact (Prod.mk.inj e').1
      subst ht
      exact nonvacuous_generated_holds (F := ZMod p) (K := K) stc hK pOrbit hcap n hreq hresp hcard cwa wg mef
        hinterCard hhon hprl hmore hord hordM hrows hsB hfB hG hp64 hzX
        (Nock.RedTeam.Batch1250.hF_zmod p))
  exact ⟨P, h1, h2, h3, h4⟩


open Nock.NockVMROM.Thm54.TraceGen.GoodSeed in
/-- **The semantic `p8` fired at the §1 package**: the package of `nonvacuous_zmod_holds`, with
`holds_of_traces`'s conclusion (through the premises, not through `hrun`). -/
theorem nonvacuous_zmod_semantic
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
        ∧ HoldsAt package
        ∧ ∃ fuel', FieldEmbedding.evalGBy (ringChar K) fuel' package.optimized.verifier.raw.claim.subject
            package.optimized.verifier.raw.claim.formula = some package.optimized.verifier.raw.claim.result ∧
          Nock.evalN fuel' package.optimized.verifier.raw.claim.subject
            package.optimized.verifier.raw.claim.formula = some package.optimized.verifier.raw.claim.result := by
  obtain ⟨P, h1, h2, h3, h4⟩ := nonvacuous_zmod_holds α lmb hrun hbound hs hf hΛp hp hp64 hK hF hwin hKszChar
  exact ⟨P, h1, h2, h3, h4, holds_of_premises P _ _ _ h4⟩

end Zmod

end

end Nock.RedTeam.Batch1310

#print axioms Nock.RedTeam.Batch1310.holds_of_premises
#print axioms Nock.RedTeam.Batch1310.nonvacuous_generated_holds
#print axioms Nock.RedTeam.Batch1310.nonvacuous_zmod_holds
#print axioms Nock.RedTeam.Batch1310.nonvacuous_zmod_semantic
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.rootResult_bridge
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.holds_of_traces
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.holds_exists
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.wrong_claim_inside_events
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.holds_of_acceptance
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.wrong_claim_rejected
#print axioms Nock.NockVMROM.Thm54.RootResultBridge.tracesWalkHyps_of_acc
