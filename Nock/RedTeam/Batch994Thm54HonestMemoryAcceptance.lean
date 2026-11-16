/-
  Nock/RedTeam/Batch994Thm54HonestMemoryAcceptance.lean

  **Read set (measured).**  Over the deployed memory mixed gate list `paperKGates` (the
  `𝕂`-valued transition bucket the family memory chip commits, `MixedCoordinateCompiler`
  `Var.challenge q` = memory `𝕂` slot `q`): slot `2` (the γ `hchalM` pins) is read by NO gate
  (`k2_unread`); positive controls: slot `4` (IO γ) and slot `3` (memory walk α) ARE read
  (`k4_read`, `k3_read`).  So slot `2` is not why honest acceptance fails.

  **Slot `3` decides it.**  The family memory chip at tuple `c` reads `alphaM c.1` at slot `3`,
  and its committed boundary gate `firstMask · (ln − chal 3)` forces `ln(row 0) = alphaM c.1` on
  every accepted trace (`MemoryWalkDeployed.walkLn_row0`).  The canonical memory trace of a
  built package has `ln(row 0) = I.memoryWalkAlpha` (its walk certificate, `WalkSat.ln1`).  At
  the honest tuple `alphaM = objects α` (the timestamp α).  Hence
  `honest_memory_acceptance_forces_walk_alpha`: at every built package, acceptance of the
  canonical memory trace by the family memory chip at the honest tuple forces
  `objects α = I.memoryWalkAlpha`.

  **Verdict at the generated package: COMPLETENESS DEFECT (conditional).**  The generated
  carrier's `α` is the §1 binder `α`; the `nockCompiles` chain passes `memoryWalkAlpha :=
  compilerWalkCoin packageOrbit` to `inputsOfCarrier` (`GenNockCompilesBounded`, F1 repair).
  `gen_honest_memory_rejected`: whenever `α ≠ memoryWalkAlpha` the canonical memory trace is
  REJECTED by the family memory chip at the generated package's honest tuple.  No §1 hypothesis
  forces `α = compilerWalkCoin`.  The chain now passes `memoryWalkAlpha := α`
  (`mwa := α` at all 34 chain sites), so `α ≠ memoryWalkAlpha` is impossible at the generated
  package and `gen_honest_memory_rejected` is vacuous there; honest acceptance at both family
  chips is `Batch1061.gen_honest_accepted`.  The theorems below remain true as stated (they are
  about an arbitrary `memoryWalkAlpha`).
-/
import Nock.RedTeam.Batch993Thm54HgoodGenerated
import Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch994

open Nock Nock.Walk
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.RedTeam.Batch906
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

/-! ## A. The read set of the deployed memory mixed gates -/

/-- Memory `𝕂`-slot reads (`Var.challenge q`) of a mixed gate. -/
def mixedReadsK (q : ℕ) {F : Type} [Field F] : MixedExpr F → Bool
  | .Var .challenge i => decide (i = q)
  | .Var _ _ | .Const _ | .Lift _ => false
  | .Scale _ x | .Neg x | .Pow x _ => mixedReadsK q x
  | .Add x y | .Sub x y | .Mul x y => mixedReadsK q x || mixedReadsK q y

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Memory `𝕂` slot `2` is read by no deployed mixed memory gate. -/
theorem k2_unread : (paperKGates (F := ZMod 5) (K := ZMod 5)).any (mixedReadsK 2) = false := by
  decide

/-- Positive control: the IO γ slot `4` is read. -/
theorem k4_read : (paperKGates (F := ZMod 5) (K := ZMod 5)).any (mixedReadsK 4) = true := by
  decide

/-- Positive control, and the slot that decides honest acceptance: the walk α slot `3` is read. -/
theorem k3_read : (paperKGates (F := ZMod 5) (K := ZMod 5)).any (mixedReadsK 3) = true := by
  decide

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## B. At every built package -/

/-- The canonical memory trace's walk line at row `0` is the family memory walk coin. -/
theorem canonical_ln_row0 (E : BuildableNockExecution F K) (I : Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    let P := buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF
    (P.memorySourceEnv (canonicalMemoryTrace P)
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).trace MemoryWalkLabel.lnRole =
      I.memoryWalkAlpha := by
  intro P
  rw [canonical_memorySourceEnv]
  have h := MemoryWalkLabelCanonical.canonical_walkRole_cur P.optimized.sampled
    P.optimized.memoryNodes P.optimized.memoryNodes_injective P.optimized.basis
    P.optimized.memoryChallenge P.optimized.memoryPublic P.optimized.orbit
    ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩ 0
  simp only [Fin.val_zero, Nat.add_zero] at h
  rw [show MemoryWalkLabel.lnRole = 31 from rfl, h]
  have hsix := ((sampledAssignment E I).exact.satisfies_iff_six_families).1
    (exactFamilyCompletion E I).six
  have hcert := ((sampledAssignment E I).exact.memoryWalkRAP_wholeTrace_iff).1 hsix.2.2.2.1
  have hln1 := hcert.1.ln1
  simp only [exactMemoryWalkRowEnv, Nock.Reified.Trans.walkRowEnvMasked]
  exact hln1

/-- **At every built package: honest memory acceptance at the honest tuple forces
`objects α = I.memoryWalkAlpha`.** -/
theorem honest_memory_acceptance_forces_walk_alpha (E : BuildableNockExecution F K) (I : Inputs E)
    (R : CommitmentResidual E)
    (hzero : I.computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F)
    (hsat : RAP.SatisfiesWithPreprocessing
      ((buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).memoryChipAt
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple)
      (QmH (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF))) :
    E.cfg.challenges.α = I.memoryWalkAlpha := by
  have h := MemoryWalkDeployed.walkLn_row0 _ _ _ hsat
  have hc := canonical_ln_row0 E I R hzero hprl hmore hord hordM hrows hgenF hF
  simp only [MemoryWalkDeployed.envK, MemoryWalkDeployed.Qmh, honestQm_QmH] at h
  have heq : (FamilyComputeRows.memorySourceEnvAt
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF)
        (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple
        (canonicalMemoryTrace (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF))
        (MemoryWalkDeployed.firstMem _)).trace MemoryWalkLabel.lnRole =
      ((buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF).memorySourceEnv
        (canonicalMemoryTrace (buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF))
        ⟨0, (buildFullPackage E I R hzero hprl hmore hord hordM
          hrows).optimized.family.problem.cfg.memRows_pos⟩).trace MemoryWalkLabel.lnRole := rfl
  rw [heq, hc] at h
  exact h.symm.trans rfl

/-! ## C. At the generated package: the canonical memory trace is rejected when `α ≠ mwa` -/

section Generated

open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
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


/-- **Completeness defect, compiled.**  At the generated package, if the §1 timestamp coin `α`
differs from the memory walk coin `mwa` passed to `inputsOfCarrier` (the chain passes
`compilerWalkCoin packageOrbit`), the canonical memory trace is NOT accepted by the family
memory chip at the package's honest tuple: the boundary gate `firstMask · (ln − chal 3)` reads
`α` at slot `3` while the honest line starts at `mwa`. -/
theorem gen_honest_memory_rejected
    (stc : NodeEncoding.StateTagChar K) (bas : Module.Basis (Fin 3) F K) {hOrb : ℕ}
    (pOrbit : StrictExtension.StrictOrbitDomain F 3 hOrb)
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
        hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).computeWalkAlpha)
    (hordM : 2 ≤ (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows → (genBuildableOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst).cfg.memRows ≤ orderOf (inputsOfCarrier (genBuildableOfProgram (F := F) (q :=
        q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos
        hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap
        hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard
        hhon).memoryWalkAlpha)
    (hrows : 3 * (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.compRows < ringChar K ∧
        (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit
        horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad
        hout hKszChar hprogCap hmemCap hfirst).cfg.memRows < ringChar K)
    {fuelG : ℕ} {rG : Noun} (hG : FieldEmbedding.evalGBy q fuelG subject formula = some rG)
    (hF : GeneratedField.PrimeFieldElems F)
    (hne : α ≠ mwa) :
    ¬ RAP.SatisfiesWithPreprocessing ((buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ
        := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
        hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp
        hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ :=
        Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas
        pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).memoryChipAt (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α
        hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB
        hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp
        hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ :=
        Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas
        pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows).honestTuple) (QmH (buildFullPackage (genBuildableOfProgram (F := F) (q := q) (Λ := Λ)
        z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B
        hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
        (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal
        hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb
        hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp
        hcard cwa mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F :=
        F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf
        hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap
        hmemCap hfirst)) (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ :=
        Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem
        B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas
        pOrbit hcap n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM
        hrows)) := by
  intro hsat
  have h := honest_memory_acceptance_forces_walk_alpha (genBuildableOfProgram (F := F) (q := q) (Λ
      := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
      hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst)
      (inputsOfCarrier (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp
      hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
      haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq hresp hcard cwa
      mwa wg msc mef hinterCard hhon) (commitmentResidualOfZero (genDataOfProgram (F := F) (q := q)
      (Λ := Λ) z α hz htwo a b c chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp
      hmem B hB hwin hKsz hKsz2 hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst))
    (inputsOfCarrier_challenges (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c
        chal hinp hmi Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2
        hb hq hchar haxis hbad hout hKszChar hprogCap hmemCap hfirst) stc bas pOrbit hcap n hreq
        hresp hcard cwa mwa wg msc mef hinterCard hhon) hprl hmore hord hordM hrows (by claim_generated) hF hsat
  have hαeq : chal.α = α := by
    have hproj := congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    simpa [ChallengeVector.computeInputs] using hproj
  exact hne (hαeq.symm.trans h)

end Generated

end

end Nock.RedTeam.Batch994

#print axioms Nock.RedTeam.Batch994.k2_unread
#print axioms Nock.RedTeam.Batch994.k4_read
#print axioms Nock.RedTeam.Batch994.k3_read
#print axioms Nock.RedTeam.Batch994.canonical_ln_row0
#print axioms Nock.RedTeam.Batch994.honest_memory_acceptance_forces_walk_alpha
#print axioms Nock.RedTeam.Batch994.gen_honest_memory_rejected
