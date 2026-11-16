/-
  Nock/RedTeam/Batch1011Thm54AxisViewBindsAtCoin.lean

  Additive.

  On accepted family traces outside `optimizedFailureEvent` (`wrapJoin`'s premises `hacc`, `hgood`,
  `hax`, `hbasis`, `hwidth`), at the round-0 strategy with the a-bearing skeleton
  (`StrategyOfTracesR0A.strategyOfTracesR0A`), every premise of the a-bearing binding theorem is
  discharged on the forest `BindsAtCoin` reads, except two named facts:

  | premise | source |
  |---|---|
  | `hz` | `c ∉ event` (`nprSeed_ne_of_good_at`) |
  | `htop` | `Batch974.wrapJoin` (acceptance + `c ∉ event` + `of_package`'s Form R side conditions) |
  | `hseed` | definitional: every node is some `lblMAt k`, whose `z` is `nprSeed c.1` (`label_of_inTree`) |
  | `haxisA` | `Batch973.read_row_facts` / `verify_row_facts` at the position `axOfRowsR0` chose (`axisFacts_at`) |
  | `hver` | `read_root`: the ver gate (`readSel_ver_at`); `verify_child`: `ver = 1` would make the row and its `intermediate` partner two `ver = 1` rows with one `reqIdx` (`ver_reqIdx_injective_at`), one row with two selectors (`verify_ver_ne_one`); `decompose` / `halt`: `ver = 1` puts the zero record's `ts = 0` equal to `α^e` (`ts_eq_alpha_pow_natLift_at`), so `α = 0` (`padding_ver_ne_one`, needs **`hα0 : alphaM c.1 ≠ 0`**) |
  | `hservedChild` | the `read_root` row's `intermediate` partner is a `verify_child` row with the same record (`paired_records_of_rowsBound_at`, `read_partner_at`), whose `eqBlk` makes `mem.child` its own `pt.noun` |
  | `hservedRoot` | `verify_partner_at` the other way round, `eqBlk` at the `read_root` partner |
  | `hleaves`, `hstructF` | topology + seed (`forestFPFacts_of_topology`) + the halt gate `sel_halt·(leaf − algebraMap atom)` (`decodeMemPub_halt_leaf_eq_atom`), needs **`hF : ∀ x : F, ∃ n < ringChar F, (n : F) = x`** (`F` its own prime field; true at `nockCompiles_zmod`, `F = ZMod p`) |

  The two carried facts: `hα0` (source: `ResponseTsMemPowers.alphaM_ne_zero_of_good_two` when the
  trace has two or more requests, `alphaM_ne_zero_of_two`; UNDISCHARGED at one request), and `hF`
  (a §1-shaped fact: `nockCompiles_zmod` fixes `F = ZMod p`, `hF_zmod`; UNDISCHARGED at a generic
  `F`).
-/
import Nock.RedTeam.Batch1010Thm54AxisViewMemoryTreeBinds
import Nock.RedTeam.Batch974Thm54Round0WrapJoinForest
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.NockVMROM.Thm54.ResponseTsMemPowers
import Nock.NockVMROM.Thm54.P8Core.Batch1011Thm54AxisViewBindsAtCoin
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1011

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf)
open Nock.RedTeam.Batch516 (ServedFingerprint)
open Nock.RedTeam.Batch973 (expR)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-! ## A. The decoded forest and its nodes -/

/-! ## B. Row facts (definitional reads of the decoded label) -/

/-! ## C. `eqBlk` at every row, and its two record halves -/

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hacc hgood hax hbasis hwidth

/-! ## D. `haxisA`: the a-bearing axis facts at every row -/

/-! ## E. `hver`: the honest `ver` at every row -/

/-! ## F. The served halves (`hservedChild`, `hservedRoot`) -/

/-! ## G. The halt leaves (`hleaves`, `hstructF`) -/

omit hacc hgood hax hbasis hwidth in
/-- `hF` at the prime field. -/
theorem hF_zmod {p : ℕ} [Fact p.Prime] :
    ∀ x : ZMod p, ∃ n : ℕ, n < ringChar (ZMod p) ∧ (n : ZMod p) = x := fun x =>
  ⟨x.val, by rw [ZMod.ringChar_zmod_n]; exact ZMod.val_lt x, ZMod.natCast_zmod_val x⟩

omit hacc hax hbasis hwidth in
/-- `hα0` from the priced α-collision event when the trace has two or more requests. -/
theorem alphaM_ne_zero_of_two (hD : 2 ≤ (P.hostileRequests (honestQc P c Qc)).length) :
    alphaM c.1 ≠ 0 :=
  ResponseTsMemPowers.alphaM_ne_zero_of_good_two P (honestQc P c Qc) (honestQm P c Qm) c hgood hD

/-! ## H. Assembly -/

/-- The seed conjunct is definitional
(`specializedCfg_R0A_z`), the memory conjunct is `memoryForestBinds_R0A`, the two BFS row
conjuncts are derived (`BindsAt.ofTreeBindings`). -/
theorem bindsAtCoin_R0A_of_computeTree
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0)
    (hcomp : ∀ hz : nprSeed c.1 ≠ 0,
      ComputeTreeBinds (nprSeed c.1)
        (strategyOfTracesR0A P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).skeleton.computeTree
        ((strategyOfTracesR0A P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).specializedExec
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).computeTree) :
    (strategyOfTracesR0A P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).BindsAtCoin
      c.1 c.2.2.2.lambda := by
  intro hz
  exact BindsAt.ofTreeBindings rfl (hcomp hz)
    (memoryForestBinds_R0A P c Qc Qm hacc hgood hax hbasis hwidth h hz hF hα0)

end

end Nock.RedTeam.Batch1011

#print axioms Nock.RedTeam.Batch1011.label_of_inTree
#print axioms Nock.RedTeam.Batch1011.axisFacts_at
#print axioms Nock.RedTeam.Batch1011.verify_ver_ne_one
#print axioms Nock.RedTeam.Batch1011.padding_ver_ne_one
#print axioms Nock.RedTeam.Batch1011.ver_at
#print axioms Nock.RedTeam.Batch1011.servedChild_at
#print axioms Nock.RedTeam.Batch1011.servedRoot_at
#print axioms Nock.RedTeam.Batch1011.haltLeaf_at
#print axioms Nock.RedTeam.Batch1011.hF_zmod
#print axioms Nock.RedTeam.Batch1011.alphaM_ne_zero_of_two
#print axioms Nock.RedTeam.Batch1011.memoryForestBinds_R0A
#print axioms Nock.RedTeam.Batch1011.bindsAtCoin_R0A_of_computeTree
