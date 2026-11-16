/-
  Nock/RedTeam/Batch974Thm54Round0WrapJoinForest.lean

  **Lane `2b-round0-wrap`: `wrapJoin` assembled.**  The round-0 wrap-then-specialize is
  the identity on every decoded memory row (`wrapR0_identity`), so the round-0 strategy's
  specialized memory forest IS the decoded forest of `execOfTraces`
  (`specialized_memoryForest_R0_eq`), and its every tree satisfies the β-free per-node predicate
  `FmemTopo` (**`wrapJoin`**) on the forest `ProductionStrategy.BindsAtCoin` reads.

  `topologyPremiseOnly_memoryTreeBinds_R0` only checks that `wrapJoin` fills the TOPOLOGY slot of
  `Batch524.memoryTreeBinds_of_topology'` on that forest.  Its other premises
  are UNDISCHARGED here (`hseed` true by definition but not proved; `hleaves`, `hver`, `hservedChild`,
  `hservedRoot`, `hstructF`).

  Derived inside:
  `FamilyIOGood` (`hio_of_hgood`), `hrb` (`P.rowsBound`), `hb1` (from `FormRBasis`).  No `25 ≤ p`, no
  `hW`, no `hpow`, no `ReadVerifyNested`, no new package field.
-/
import Nock.RedTeam.Batch973Thm54Round0WrapJoin
import Nock.RedTeam.Batch524Thm54DecodeMemoryRowIn
import Nock.RedTeam.Batch884Thm54Part2aFamIOInstance
import Nock.NockVMROM.Thm54.P8Core.Batch974Thm54Round0WrapJoinForest
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch974

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch973
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.RedTeam.Batch516 (ServedFingerprint)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hacc hgood hax hbasis hwidth

/-- **Topology premise ONLY — not a step toward `BindsAtCoin`.**  `Batch524.memoryTreeBinds_of_topology'`
on a tree of the round-0 specialized forest with its `htop` filled by `wrapJoin` and `hz` given.  `hseed` holds by definition but is not proved;
`hleaves`, `hver`, `hservedChild`, `hservedRoot`, `hstructF` are UNDISCHARGED. -/
theorem topologyPremiseOnly_memoryTreeBinds_R0
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0) {q : ℕ}
    (forest : List (NTree (MState × DTmem K)))
    (t : NTree (MState × DTmem K))
    (ht : t ∈ ((strategyOfTracesR0 P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest)
    (hseed : ∀ node, InTree t node → node.label.2.1.z = nprSeed c.1)
    (hleaves : MemoryLeafAtomsRealized q t)
    (hver : ∀ node, InTree t node → node.label.2.2.ver = decide (node.label.1 = .read_root))
    (hservedChild : ∀ node, InTree t node → node.label.1 = .read_root →
      ServedFingerprint forest node.label.2.2.mem.child)
    (hservedRoot : ∀ node, InTree t node → node.label.1 = .verify_child →
      ServedFingerprint forest node.label.2.2.mem.root)
    (haxis : ∀ node, InTree t node → memoryMemRecKind node.label.1 = .active →
      Batch524.AxisInWindow q node.label.2.2.mem.axis)
    (hstructF : Batch524.ForestFPFacts (nprSeed c.1) q forest) :
    Batch524.MemoryTreeBindsA (nprSeed c.1) (decodeMemoryTree q forest t) t :=
  Batch524.memoryTreeBinds_of_topology' hz forest t
    (wrapJoin P c Qc Qm hacc hgood hax hbasis hwidth h hz t ht)
    hseed hleaves hver hservedChild hservedRoot haxis hstructF

end

end Nock.RedTeam.Batch974

#print axioms Nock.RedTeam.Batch974.hio_of_hgood
#print axioms Nock.RedTeam.Batch974.row_identity
#print axioms Nock.RedTeam.Batch974.wrapR0_identity
#print axioms Nock.RedTeam.Batch974.specialized_memoryForest_R0_eq
#print axioms Nock.RedTeam.Batch974.wrapJoin
#print axioms Nock.RedTeam.Batch974.topologyPremiseOnly_memoryTreeBinds_R0
