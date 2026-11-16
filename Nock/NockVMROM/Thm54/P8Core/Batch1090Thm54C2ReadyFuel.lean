/-
  Nock/NockVMROM/Thm54/P8Core/Batch1090Thm54C2ReadyFuel.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1090Thm54C2ReadyFuel`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1090Thm54C2ReadyFuel.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1024Thm54C2BindsAtCoin
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.Batch1090Thm54C2ReadyFuel
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1090

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1021
open Nock.RedTeam.Batch525
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]
variable {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}
set_option quotPrecheck false
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

/-- `ComputeTreeBinds` of the C2 join from the chip-side bundle and the root subject binding. -/
theorem computeTreeBinds_of_chipReady {z : K} (hz : z ≠ 0) {q fuel : ℕ}
    {t : NTree ((State × DTcomp K) × ℕ)} {subj formula : Noun}
    (hfuel : t.size ≤ fuel)
    (hC : C2ChipReady (sv := sv) (ax := ax) z q t subj formula)
    (hs : bindFP z subj t.label.1.2.2.1.s) :
    ComputeTreeBinds z (J fuel t subj formula) (mapNTree Prod.fst t) :=
  computeTreeBinds_of_readyF hz hfuel (c2JoinReadyF_of_chipReady hz hC hs)

section AtFamily

open scoped Polynomial
open Polynomial
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.RedTeam.Batch1024
variable {F K' : Type} [Field F] [Field K'] [Algebra F K']
  [Fintype F] [DecidableEq F]
  [Fintype K'] [DecidableEq K'] [CharP K' (ringChar K')] [FiniteDimensional F K']
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K' hOrb)
  (c : OptimizedProductionChallengeTuple K' F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)

/-- **`hcomp` at the C2 strategy from the chip-side bundle**: `C2ChipReady` of the S-carrying tree
and the ROOT subject binding (every other subject binding is derived). -/
theorem hcomp_C2_of_chipReady (hz : nprSeed c.1 ≠ 0) {q : ℕ}
    (hC : C2ChipReady (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) q (treeS P c Qc)
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula)
    (hsRoot : bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.subject
      (treeS P c Qc).label.1.2.2.1.s) :
    ComputeTreeBinds (nprSeed c.1) (TC P c Qc Qm h).skeleton.computeTree
      ((TC P c Qc Qm h).specializedExec (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree := by
  rw [specialized_computeTree_C2]
  have h1 := computeTreeBinds_of_chipReady hz (Nat.le_refl (treeS P c Qc).size) hC hsRoot
  rw [c2TreeOfTraces_fst P.optimized (honestQc P c Qc) (honestQm P c Qm) c h] at h1
  exact computeTreeBinds_mapNTree _ (fun s row hb => bindComputeRow_specialize (alphaM c.1) s row hb)
    _ _ _ (Nat.le_refl _) h1

theorem bindsAtCoin_C2_of_chipReady
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0) {q : ℕ}
    (hC : C2ChipReady (sv := svF P c Qm) (ax := axF P c Qc) (nprSeed c.1) q (treeS P c Qc)
      P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula)
    (hsRoot : bindFP (nprSeed c.1) P.optimized.verifier.raw.claim.subject
      (treeS P c Qc).label.1.2.2.1.s) :
    (TC P c Qc Qm h).BindsAtCoin c.1 c.2.2.2.lambda := by
  intro hz
  exact BindsAt.ofTreeBindings rfl (hcomp_C2_of_chipReady P c Qc Qm h hz hC hsRoot)
    (memoryForestBinds_C2 P c Qc Qm h hacc hgood hax hbasis hwidth hz hF hα0)

end AtFamily

end Nock.RedTeam.Batch1090
