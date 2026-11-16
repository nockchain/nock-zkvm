/-
  Nock/RedTeam/Batch990Thm54HonestPoleChooser.lean

  **Component 4 (internal-pole pairs).**  `inputsOfCarrier` now chooses its internal pole with
  `BuildableChips.interPoleOfE'`, which also excludes `-γ^8` (the padding rows' record RLC,
  `Batch957.honest_pair_hit_of_pole_neg_gamma8`); the slack is
  `BuildableChips.interCard'_of_basis` (no new hypothesis).  So at every package built from
  `inputsOfCarrier` both closed-form side conditions hold (`inter_sides_inputsOfCarrier`):
  `interNe` (`h0`) and `interGamma8` (`hγ8`).

  **`hzc` (`inactiveCprime`).**  Every generated a-bearing memory row has `cprime? = none`
  (`genMemoryForest_bfs_aBearing`), the row encode changes `cprime?` only on active rows
  (`MemoryRowTemplate.encodeRow`), and acceptance gives `row.1 = row.2.2.st`.  So every
  `decompose` / `halt` row of the generated execution has `C' = 1` (`gen_inactiveCprime`).

  **`HonestFill` STOPs on `hchalM` (compiled).**  At ANY package, `hchalM` (the family memory
  chip's `chalVal` at the honest tuple equals the package's) forces the sampled IO `γ` to be the
  memory table's `γ` (`hchalM_forces_gamma`): memory `𝕂` slot `2` reads `c.2.1.1` (the IO `γ`)
  on the family side (`memoryKOfTuple`) and the table `γ` on the package side
  (`memoryCoordinatePins.memoryChallenge`).  The generated carrier has
  `chal.memoryInputs = memInputs z = ⟨z, 0, 0⟩`, so the table `γ` is `0`
  (`gen_table_gamma_zero`), and `HonestFill` at a generated package forces the CHOSEN IO coin
  `(ioCoinsOfCarrier..).gamma = 0` (`Batch991.honestFill_generated_forces_gamma_zero`).
-/
import Nock.RedTeam.Batch963Thm54HonestEventAssembly
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch990

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.RedTeam.Batch906

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

/-! ## A. `hchalM` forces the IO `γ` to be the table `γ` (any package) -/

/-- **At any package, `hchalM` forces `sampled IO γ = table γ`** (memory `𝕂` slot `2`). -/
theorem hchalM_forces_gamma (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (h : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
      P.optimized.memoryChallenge) :
    P.optimized.sampled.sampled.coins.gamma =
      P.optimized.family.problem.cfg.challenges.γ := by
  have hpin := P.optimized.memoryCoordinatePins.memoryChallenge ⟨2, by decide⟩
  have hslot : ∀ k : Fin 3,
      P.optimized.memoryChallenge (6 + 3 * ((⟨2, by decide⟩ : Fin 3) : ℕ) + (k : ℕ)) =
        CoordinateBasis.coord P.optimized.basis
          (DeployedChipFamily.memoryKOfTuple P.honestTuple 2) k := by
    intro k
    rw [← h]
    exact DeployedChipFamily.memoryChalValOfTuple_slot P.optimized.basis P.honestTuple
      ⟨2, by decide⟩ k
  simp only [hslot] at hpin
  have hrec := CoordinateBasis.reconstruct_coord P.optimized.basis
    (DeployedChipFamily.memoryKOfTuple P.honestTuple 2)
  simp only [CoordinateBasis.reconstruct] at hrec
  rw [hrec] at hpin
  simpa [DeployedChipFamily.memoryKOfTuple, OptimizedFullStrictNockVMROMPackage.honestTuple,
    OptimizedFullStrictNockVMROMPackage.honestProductionTuple, exactMemoryRowEnv,
    Reified.memoryEnvFull, ChallengeVector.memoryInputs] using hpin

/-- `HonestFill` (through its `hchalM` field) forces the same equality. -/
theorem honestFill_forces_gamma {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
    (H : HonestFill P) :
    P.optimized.sampled.sampled.coins.gamma =
      P.optimized.family.problem.cfg.challenges.γ :=
  hchalM_forces_gamma P H.hchalM

/-! ## B. Component 4's side conditions at every package built from `inputsOfCarrier` -/

open Nock.NockVMROM.Thm54.TraceGen in
/-- **Component 4's two closed-form side conditions** (`interNe`, `interGamma8`) at every
package built from `inputsOfCarrier` (the generated packages' inputs). -/
theorem inter_sides_inputsOfCarrier
    (E : BuildableNockExecution F K) {hOrb' : ℕ}
    (stc : NodeEncoding.StateTagChar K)
    (b : Module.Basis (Fin 3) F K)
    (orbit : StrictExtension.StrictOrbitDomain F 3 hOrb')
    (hcap : 2 ^ E.cfg.orbit.h ≤ 2 ^ hOrb')
    (n : ℕ)
    (hreq : E.exec.derivedRequestIO.length ≤ n)
    (hresp : E.exec.derivedResponseIO.length ≤ n)
    (hcard : RecordCarrier.honestIOBound n n (Fintype.card K) < Fintype.card (K × K))
    (cwa mwa wg : K) (msc : Fin 4 → F) (mef : K)
    (hinterCard : 4 * E.cfg.memRows + 1 < Fintype.card K)
    (hhon : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (R : CommitmentResidual E)
    (hzero : (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef
        hinterCard hhon).computeChallenges =
      (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
    (hprl : RowLayout.PairedRecordLayout E.exec)
    (hmore : BuildableAxisWitness.LaterSeedZeros E)
    (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf (inputsOfCarrier E stc b orbit hcap
      n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon).computeWalkAlpha)
    (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf (inputsOfCarrier E stc b orbit hcap
      n hreq hresp hcard cwa mwa wg msc mef hinterCard hhon).memoryWalkAlpha)
    (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
    (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
    (hF : GeneratedField.PrimeFieldElems F) :
    (buildFullPackage E (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc
        mef hinterCard hhon) R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled.interPole ≠ 0 ∧
      (buildFullPackage E (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc
          mef hinterCard hhon) R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled.interPole +
        (buildFullPackage E (inputsOfCarrier E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc
          mef hinterCard hhon) R hzero hprl hmore hord hordM
            hrows).optimized.sampled.sampled.coins.gamma ^ 8 ≠ 0 :=
  inputsOfCarrier_interPole_sides E stc b orbit hcap n hreq hresp hcard cwa mwa wg msc mef
    hinterCard hhon

/-! ## C. `hzc` (`inactiveCprime`) -/

/-- On an accepted execution whose inactive rows leave `cprime?` unset, every `decompose` /
`halt` row has `C' = 1`. -/
theorem inactiveCprime_of_rows {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (hacc : exec.MemoryRowsAccepted)
    (hrows : ∀ row ∈ exec.memoryRows,
      memoryMemRecKind row.1 ≠ .active → row.2.2.cprime? = none)
    (i : Fin cfg.memRows)
    (h1 : (exec.memoryPubAt i).st ≠ .read_root) (h2 : (exec.memoryPubAt i).st ≠ .verify_child) :
    (exec.memoryPubAt i).cprime = 1 := by
  have hmem := exec.memoryRowAt_mem i
  have hrow := List.forall_iff_forall_mem.1 hacc _ hmem
  have hst : (exec.memoryRowAt i).1 = (exec.memoryRowAt i).2.2.st := hrow.1
  have hk : memoryMemRecKind (exec.memoryRowAt i).1 ≠ .active := by
    rw [hst]
    change memoryMemRecKind (exec.memoryPubAt i).st ≠ _
    cases h : (exec.memoryPubAt i).st with
    | decompose => simp [memoryMemRecKind]
    | halt => simp [memoryMemRecKind]
    | read_root => exact absurd h h1
    | verify_child => exact absurd h h2
  have hnone := hrows _ hmem hk
  change ((exec.memoryRowAt i).2.2.cprime?).getD 1 = 1
  rw [hnone]
  rfl

/-! ## D. At the generated carrier -/

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

/-- **`hzc` at the generated carrier**: every `decompose` / `halt` row has `C' = 1`. -/
theorem gen_inactiveCprime :
    ∀ i : Fin (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.memRows,
      ((genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryPubAt i).st ≠ .read_root →
      ((genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryPubAt i).st ≠ .verify_child →
      ((genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).exec.memoryPubAt i).cprime = 1 := by
  intro i h1 h2
  refine inactiveCprime_of_rows _ (BuildablePackage.memoryRowsAccepted _) ?_ i h1 h2
  intro row hrow hk
  change row ∈ (genExactExecution (F := F) chal Ksz orbit horb a b c (genComputeRows z α t)
    (genMemoryForest z α chal.lam (memInputs z) t) hmempos hcomp hmem).memoryRows at hrow
  rw [genExactExecution_memoryRows] at hrow
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hrow
  have hk' : memoryMemRecKind (GenMemoryRow.row n.label).1 ≠ .active := hk
  have hA := (genMemoryForest_bfs_aBearing (lmb := chal.lam) z α (memInputs z) t n hn).1
  simp only [MemoryRowTemplate.encodeRow, if_neg hk']
  exact hA

/-- The generated carrier's memory-table `γ` is `0` (`hmi : chal.memoryInputs = memInputs z`). -/
theorem gen_table_gamma_zero :
    (genBuildableOfProgram (F := F) (q := q) (Λ := Λ) z α hz htwo a b c chal hinp hmi
        Ksz orbit horb h hseed hcoins hΛ hconf hmempos hcomp hmem B hB hwin hKsz hKsz2 hb hq hchar
        haxis hbad hout hKszChar hprogCap hmemCap hfirst).cfg.challenges.γ = 0 := by
  have hproj := congrArg (fun inp : MemoryTable.Inputs K => inp.γ) hmi
  show chal.γ = 0
  simpa [ChallengeVector.memoryInputs, memInputs] using hproj

end Generated

end

end Nock.RedTeam.Batch990

#print axioms Nock.RedTeam.Batch990.hchalM_forces_gamma
#print axioms Nock.RedTeam.Batch990.honestFill_forces_gamma
#print axioms Nock.RedTeam.Batch990.inter_sides_inputsOfCarrier
#print axioms Nock.RedTeam.Batch990.inactiveCprime_of_rows
#print axioms Nock.RedTeam.Batch990.gen_inactiveCprime
#print axioms Nock.RedTeam.Batch990.gen_table_gamma_zero
