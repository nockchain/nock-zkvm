/-
  Nock/RedTeam/Batch993Thm54HgoodGenerated.lean

  Every field of `Batch992.HgoodFill` (the eight `HonestFill` fields `hgood` consumes; `hchalM`
  is not among them) has a source at the generated package, with the basis the chain uses
  (`compilerBasis hK`, `nockCompiles_p68`):

  * `hax` -- `GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound` through
    `formRAxisBound_iff_rows` (exactly as `nockCompiles_p68` discharges it);
  * `hwidth` -- `GenFormRAxisLambda.FormRWidth_of_hp64`;
  * `hC` -- `Batch991.gen_cprimeCoherent`;
  * `hchalC` -- `chalValOfTuple_honest` below slot `36`, both sides `0` above
    (`hchalC_built`, every built package);
  * `hst` -- `genComputeSkeleton_root_state` through the root row's render
    (`genComputeRows_label_skel`, `renderNode_row_state`) and `genDataOfProgram_publicClaim`;
  * `hs` / `hf` / `he` -- `BindsAt.root_bindings` at `Data.honest_binds` (`root_sfe_built`,
    every built zero-array package; as `GenericHonestArrays.mixed_root_bindings`).

  The extra binders `hK`, `hsB`, `hfB`, `hG`, `hp64` are the `nockCompiles` chain's own (§1
  `hK`, `hs`, `hf`, `hp64`; `hG` is `evalGRom_le_evalGBy hgrom` in `nockCompiles_p68`), not new
  premises.  `hgood_generated'` is `hgood` at the generated package with only `hlam`
  (component 11) and `hpair` (component 12) beyond them.
-/
import Nock.RedTeam.Batch992Thm54HgoodFill
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch993

open Nock Nock.Walk
open Nock.Framework.Thm54
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

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## Built-package sources -/

/-- **`hchalC` at every built package.** -/
theorem hchalC_built (E : BuildableNockExecution F K) (I : Inputs E) (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    DeployedChipFamily.computeChalValOfTuple
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple =
      (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.computeChallenge := by
  funext j
  by_cases hj : j < 36
  · have hq : j / 3 < 12 := by omega
    have hk : j % 3 < 3 := Nat.mod_lt _ (by decide)
    have h := (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).chalValOfTuple_honest
      ⟨j / 3, hq⟩ ⟨j % 3, hk⟩
    have hj' : 3 * (j / 3) + j % 3 = j := Nat.div_add_mod j 3
    simp only [hj'] at h
    exact h
  · have hl : DeployedChipFamily.computeChalValOfTuple
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple j = 0 := by
      simp only [DeployedChipFamily.computeChalValOfTuple, if_neg hj]
    rw [hl]
    show (0 : F) = BuildableChips.computeChallenge E I j
    simp [BuildableChips.computeChallenge, hj]

/-- **`hs` / `hf` / `he` at every built zero-array package**: `BindsAt.root_bindings` at
`Data.honest_binds`. -/
theorem root_sfe_built (E : BuildableNockExecution F K) (D : Data E) (I : Inputs E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K D.skeleton.publicClaim D.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    let P := buildFullPackage E I (commitmentResidualOfZero D) hzero hprl hmore hord hordM hrows hgenF hF
    (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).s =
      GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.subject ∧
    (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).f =
      GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.formula ∧
    (P.optimized.family.problem.exec.computePubAt
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩).e =
      GlobalCarryRecognizer.enc (nprSeed P.honestTuple.1) P.optimized.verifier.raw.claim.result :=
          by
  intro P
  have hroot := BindsAt.root_bindings D.honest_binds
  have hpub := computePubAt_root_eq E.exec
  change (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).s =
      GlobalCarryRecognizer.enc E.cfg.challenges.z D.skeleton.publicClaim.subject ∧
    (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).f =
      GlobalCarryRecognizer.enc E.cfg.challenges.z D.skeleton.publicClaim.formula ∧
    (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).e =
      GlobalCarryRecognizer.enc E.cfg.challenges.z D.skeleton.publicClaim.result
  rw [hpub]
  exact hroot

/-! ## At the generated package -/

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


/-- **`hst` at the generated carrier**: the root row's state is the formula's head. -/
theorem gen_root_state :
    ((genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).exec.computePubAt ⟨0, (genBuildableOfProgram (F := F)
        (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.compRows_pos⟩).state =
      ComputeWalkSeed.rootStateOfFormula formula := by
  rw [computePubAt_root_eq (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
      hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
      hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec]
  show ((mapNTree (fun g : GenComputeRow K => setRowCoins a b c g.row)
    (genComputeRows z α t)).label).2.2.1.state = _
  rw [mapNTree_label]
  show ((genComputeRows z α t).label.row).2.2.1.state = _
  rw [genComputeRows, renderRows_label_row, GenFormRAxisLambda.renderNode_row_state,
    bfsAssign_label_skel, airReorder_label]
  exact genComputeSkeleton_root_state fuel subject formula t result h

/-- **`HgoodFill` at the generated package**, every field from a named source. -/
theorem hgoodFill_generated
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
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
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
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg
        msc mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64) :
    Batch992.HgoodFill (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz
        htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
        hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF) := by
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  have hclaim : (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b
      c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
      horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
      hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
      hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
      (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h
      hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
      hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F)
      (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
      hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
      hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc
      mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).optimized.verifier.raw.claim = ⟨subject,
      formula, result⟩ :=
    genDataOfProgram_publicClaim (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
        orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis
        hbad hout hKszChar hprogCap hmemCap hfirst
  have hsfe := root_sfe_built (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
      chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
      hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (genDataOfProgram (F := F) (q :=
      q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
      hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
      hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
      pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (inputsOfCarrier_challenges
      (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
      horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
      hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n
      hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF
  refine ⟨?_, ?_, Batch991.gen_cprimeCoherent (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz :=
      hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz
      := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ :=
      hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB)
      (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis
      := haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap
      := hmemCap) (hfirst := hfirst),
    hchalC_built (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F
        := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ
        hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) _ (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF, ?_, hsfe.1, hsfe.2.1, hsfe.2.2⟩
  · have hr := GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound (q := q) (by omega) hsB hfB
      hG h (hchar.trans hFK.symm) (by rw [hchar, ← hFK]; exact hp64)
      (compilerBasis_formR (F := F) (K := K) hK) z α a b c
    rw [← genExactExecution_computeRows (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
      (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem] at hr
    exact (GenFormRAxisLambda.formRAxisBound_iff_rows _ _).2 hr
  · exact GenFormRAxisLambda.FormRWidth_of_hp64 (by rw [hFK, ← hchar]; omega) hp64
  · rw [hclaim]
    exact gen_root_state (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz := hz) (htwo := htwo) (a
        := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz := Ksz) (orbit :=
        orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ) (hconf :=
        hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB) (hwin :=
        hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis :=
        haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap
        := hmemCap) (hfirst := hfirst)

/-- **`hgood` at the generated package, components 11 and 12 the only open ones.** -/
theorem hgood_generated'
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
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
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
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg
        msc mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsB : FieldEmbedding.BoundedBy q subject) (hfB : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hp64 : ringChar F < 2 ^ 64)
    (hlam : (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).honestTuple ∉ (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
        hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
        (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
        hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).decodedLambdaEventOf (canonicalComputeTrace
        (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF))
      (canonicalMemoryTrace (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
          hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
          hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K
          := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF)))
    (hpair : (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).honestTuple.1 ∉
        PreSeedCensus.reqPairEventOfEnvs K (buildFullPackage (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K
        := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
        (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).q
      (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).optimized.family.problem.cfg.kMem
      ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).optimized.family.problem.cfg.memRows ⊔
          (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).optimized.Λ)
      ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).memoryBaseEnv (canonicalMemoryTrace
          (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF)))
      (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ :=
          Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
          hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
          (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
          hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
          hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K
          := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).strategy.skeleton)) :
    (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
        hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq
        hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).honestTuple ∉ (buildFullPackage
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier (genBuildableOfProgram (F := F) (q
        := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
        hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
        (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
        hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).optimizedFailureEvent (honestQc _
        (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero
        (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa
        mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).honestTuple (QcH _))
      (honestQm _ (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
          b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) (inputsOfCarrier
          (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz
          orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
          haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K := K) hK)
          pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
          (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
          chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
          hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
          (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo
          a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin
          hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc
          (compilerBasis (F := F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
          hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF).honestTuple (QmH _)) := by
  have hsg := Batch956.genData_seed_good (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz := hz)
      (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz :=
      Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ)
      (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB)
      (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis
      := haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap
      := hmemCap) (hfirst := hfirst)
  have htp := Batch957.gen_timestamp_premises (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz :=
      hz) (htwo := htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz
      := Ksz) (orbit := orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ :=
      hΛ) (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB)
      (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis
      := haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap
      := hmemCap) (hfirst := hfirst)
  exact Batch992.hgood_of_fill
    (hgoodFill_generated (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz := hz) (htwo := htwo) (a
        := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz := Ksz) (orbit :=
        orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ) (hconf :=
        hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB) (hwin :=
        hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis :=
        haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap) (hmemCap
        := hmemCap) (hfirst := hfirst) stc hK pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef
        hinterCard
      hhon hprl hmore hord hordM hrows hF hsB hfB hG hp64)
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb
        h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout
        hKszChar hprogCap hmemCap hfirst).traversal.1
    (Batch956.honestTuple_not_mem_failureUnion_zero (genDataOfProgram (F := F) (q := q) (Λ := Λ) z α
        hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F := F) (K :=
        K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon)
        (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a
        b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz
        hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc (compilerBasis (F :=
        F) (K := K) hK) pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl
        hmore hord hordM hrows (by claim_generated) hF
      hsg.1 hsg.2)
    htp.1 htp.2
    (Batch991.component4_generated (F := F) (q := q) (Λ := Λ) (z := z) (α := α) (hz := hz) (htwo :=
        htwo) (a := a) (b := b) (c := c) (chal := chal) (hinp := hinp) (hmi := hmi) (Ksz := Ksz)
        (orbit := orbit) (horb := horb) (h := h) (hseed := hseed) (hcoins := hcoins) (hΛ := hΛ)
        (hconf := hconf) (hmempos := hmempos) (hcomp := hcomp) (hmem := hmem) (B := B) (hB := hB)
        (hwin := hwin) (hKsz := hKsz) (hKsz2 := hKsz2) (hb := hb) (hq := hq) (hchar := hchar) (haxis
        := haxis) (hbad := hbad) (hout := hout) (hKszChar := hKszChar) (hprogCap := hprogCap)
        (hmemCap := hmemCap) (hfirst := hfirst) stc (compilerBasis (F := F) (K := K) hK) pOrbit hcap
        n hreq hresp hcard cwa mwa wg msc
      mef hinterCard hhon hprl hmore hord hordM hrows (by claim_generated) hF)
    hlam hpair

end

end Nock.RedTeam.Batch993

#print axioms Nock.RedTeam.Batch993.hchalC_built
#print axioms Nock.RedTeam.Batch993.root_sfe_built
#print axioms Nock.RedTeam.Batch993.gen_root_state
#print axioms Nock.RedTeam.Batch993.hgoodFill_generated
#print axioms Nock.RedTeam.Batch993.hgood_generated'
