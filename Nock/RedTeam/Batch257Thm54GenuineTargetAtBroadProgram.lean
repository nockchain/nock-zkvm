/-
  Nock/RedTeam/Batch257Thm54GenuineTargetAtBroadProgram.lean

  **`GenuineTargetAt` at a generator-produced program, with no free hypotheses.**

  This is the step-2 instantiation of
  `TraceGen.nockCompiles_of_accepted_genuine` (`GenGenuineTarget.lean` §9) at
  `GenBroadProgram.bpTree` — seventeen rows, eight of the eleven compute
  states, `Λ = 22`, `K = GaloisField 769 3`, seed `φ(8)`, `α = φ(4)`, coins
  `(0, 0, 1)`, `Ksz = 64` — reusing `Batch232.bp_buildable`'s and
  `Batch256`'s already-discharged side conditions verbatim.  No `decide` at a
  released carrier; the only new tactic calls are `omega`/`norm_num` on the two
  IO column bounds.

  The
  carrier is existentially quantified only to avoid transcribing
  `genBuildableOfProgram`'s thirty arguments; it is witnessed by the generator's
  own carrier.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenuineTarget
import Nock.NockVMROM.Thm54.BuildableAxisWitness
import Nock.RedTeam.Batch231Thm54BroadProgramSemanticData
import Nock.RedTeam.Batch246Thm54InputsAtGeneratedCarrier
import Nock.RedTeam.Batch256Thm54InputsAtBroadProgram
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch257

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam
open Nock.RedTeam.Batch232

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F

local instance charRingDK : CharP DK (ringChar DK) := ringChar.charP DK

noncomputable section




theorem b257_hgt : 11 < ringChar DK := by
  rw [DotConfig769.ringChar_K]; norm_num

theorem b257_genuineTarget_at_broad_program
    (hax : FormRAxisBound Batch256.bpPackage.optimized.sampled
      Batch256.bpPackage.optimized.basis)
    (hbasis : FormRBasis Batch256.bpPackage.optimized.basis)
    (hwidth : FormRWidth DF) :
    ∃ package : OptimizedFullStrictNockVMROMPackage DF DK 8,
      OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim =
            ⟨bpSubject, bpFormula, bpResult⟩
        ∧ (∃ E : BuildableNockExecution DF DK,
              ∀ a g : DK, package.strategy.Accepts (GenericHonestArrays.honestCoin E a g)
                E.cfg.challenges.lam)
        ∧ ∃ ω : JointCoins DK,
            package.strategy.Accepts ω Batch231.bpChal.lam ∧
              ω ∉ ProductionP8Containment.FailureUnion package.strategy
                    package.optimized.census Batch231.bpChal.lam ∧
              GenuineTargetAt package.strategy 769 22 ω Batch231.bpChal.lam := by
  obtain ⟨package, hstmt, hclaim, hfibre, hgen⟩ :=
    nockCompiles_of_accepted_genuine (F := DF) (q := 769) (Λ := 22)
      DotConfig769.seedZ DotConfig769.alphaA
      DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 1
      Batch231.bpChal Batch231.bp_hinp Batch231.bp_hmi
      64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
      (genComputeSkeleton_bp 0)
      Batch231.bp_seedGood_at769
      (bp_computeCoins _ _)
      (by norm_num) Batch231.bp_air_traceConfined
      Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem
      192 (le_of_eq Batch180.alphaA_order_eq_192.symm)
      (by have := Batch231.bp_accAt_le; omega)
      (by have := Batch231.bp_accAt_le; omega)
      bp_hKsz2
      Batch231.bp_hb (by norm_num) DotConfig769.ringChar_K.symm Batch231.bp_haxis
      (not_mem_badSeeds_of_pairs _ _
        (bp_pairs_sep DotConfig769.seedZ Batch231.bp_ringChar_gt_two
          (Batch231.bp_sepSeed_one_two _) _))
      Batch231.bp_hout
      bp_hKszChar bp_hprogCap bp_hmemCap
      Batch231.bp_hlt Batch232.bp_laterSeedZeros
      (hOrb := 8)
      DotConfig769.stateTagChar DotConfig769.basis DotConfig769.strictOrbit
      Batch256.b256_hOrbCap 255 (by have := Batch231.bp_accAt_le; omega)
      (by rw [bp_memRowsLen]; norm_num)
      Batch256.b256_hcard 2 2 5 (fun j => (j : DF) + 1) 2
      (fun hge => by
        change (bfsForest [genComputeRows DotConfig769.seedZ DotConfig769.alphaA
            (bpTree (K := DK))]).length ≤ orderOf (2 : DK)
        rw [Batch231.bp_genComputeRows_len]
        exact Batch246.b246_two_order_ge 17 (by norm_num))
      (fun _ => by
        change (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
            (memInputs DotConfig769.seedZ) (bpTree (K := DK)))).length ≤
          orderOf (2 : DK)
        rw [bp_memRowsLen]
        have hcast : (2 : DK) = (algebraMap DF DK).toMonoidHom (2 : DF) :=
          (map_natCast (algebraMap DF DK) 2).symm
        rw [hcast, orderOf_injective (algebraMap DF DK).toMonoidHom
          (RingHom.injective (algebraMap DF DK)) (2 : DF)]
        have : orderOf (2 : DF) = 384 :=
          Nock.NockVMROM.Thm54.TraceGen.DotConfig769.goldilocks769_two_order
        omega)
      Batch256.b256_hrows (bp_evalGBy (by norm_num)) DotConfig769.dot_primeField hax hbasis hwidth
  exact ⟨package, hstmt, hclaim, ⟨_, hfibre⟩, hgen⟩

end

end Nock.RedTeam.Batch257

#print axioms Nock.RedTeam.Batch257.b257_genuineTarget_at_broad_program
