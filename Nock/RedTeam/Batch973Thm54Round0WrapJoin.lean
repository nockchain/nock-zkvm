/-
  Nock/RedTeam/Batch973Thm54Round0WrapJoin.lean

  **Lane `2b-round0-wrap`: `wrapJoin`, the a-recovering wrap closes the `BindsAtCoin`
  chain's `eqBlk` / `FmemTopo` premise.**

  Per row:

  * `read_root` (`ver = 1`): the ten-slot record IS an active compute request's
    (`row_record_is_request_at`); slot 9 gives `e := natLift reqIdx = expOfAt a j`, the locator
    finds `(a, j)` again (`Batch823.locateExp_expOfAt`), and slots 6 / 8 are the located
    certificate's `(λ^m, C'(λ))` (`Batch823.slot_values`).  The recovered `a := certAxis m c`
    re-encodes to exactly that pair: `formRT λ a = λ^m` always, `formRC λ a = C'(λ)` by the
    certificate's padding (`Batch972.formRC_certAxis`), which R4's path validity gives because the
    row's exponent is paired in its decoded root tree (`Batch971.paired_of_read_row`,
    `Batch824.r4_path_valid_at`, `UniqueExponents` from `uniqueExponents_decoded_pkg`, `CertInRange`
    from `Batch908.hA_of_acceptance`); `a < p` by the U1 comparison gadget
    (`Batch972.certAxis_lt_ringChar`, under `FormRWidth`), so `nockAxisOf (a : 𝕂) = a`.  `ts = α^e` is
    `ts_eq_alpha_pow_natLift_at`.
  * `verify_child`: the `intermediate` partner (`verify_partner_at`) is a `read_root` row with the
    SAME ten-slot record, so the same exponent and the same `(T, C', ts)`.
  * `decompose` / `halt`: `eqBlk` zeroes the record (`Batch509.eqBlk_padding_mem_zero`, from the
    decoded forest's β-free topology `Batch501.memoryTopology_of_deployed_of_good`).
  * every row: `λ` is the memory chip's slot `8` (`memorySourceEnvAt_chal8`).

  Hence the round-0 strategy's specialized memory forest IS the decoded forest
  (`specialized_memoryForest_R0_eq`), and **`wrapJoin`**: its every tree is in
  `L_RVT^{FmemTopo,2}` — the premise `Batch524.memoryTreeBinds_of_topology'` takes on the forest
  `BindsAtCoin` reads.  Contrast `Batch912.specialized_memoryForest_eq_encode`: the lifted wrap's
  specialized forest is the decoded one with every `T` encoded once more.
-/
import Nock.RedTeam.Batch970Thm54Round0WrapReadSet
import Nock.RedTeam.Batch971Thm54Round0WrapForestCover
import Nock.RedTeam.Batch972Thm54Round0WrapCertAxis
import Nock.RedTeam.Batch824Thm54R4Bridge
import Nock.RedTeam.Batch908Thm54R4HonestShiftRange
import Nock.RedTeam.Batch501Thm54MemoryTopology
import Nock.RedTeam.Batch489Thm54FoOfEqFoW
import Nock.RedTeam.Batch940Thm54LiftStrategyReceipts
import Nock.RedTeam.Batch844Thm54HpowHW
import Nock.NockVMROM.Thm54.UniqueExponentsBridge
import Nock.NockVMROM.Thm54.HostilePoleAlignment
import Nock.NockVMROM.Thm54.P8Core.Batch973Thm54Round0WrapJoin
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch973

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch575

noncomputable section

/-! ## A. The row-level identity, abstractly -/

section Generic

variable {K : Type} [Field K]

end Generic

/-! ## B. `rowBits` through an injective embedding -/

section Embed

variable {F K : Type} [Field F] [Field K] (f : F →+* K) (hf : Function.Injective f)
include hf

end Embed

/-! ## C. At the family chips -/

section Deployed

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
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)

include hacc hgood hio hrb hb1

end Deployed

end

end Nock.RedTeam.Batch973

#print axioms Nock.RedTeam.Batch973.specialize_wrapR0_eq_self
#print axioms Nock.RedTeam.Batch973.read_row_slots
#print axioms Nock.RedTeam.Batch973.read_row_padding
#print axioms Nock.RedTeam.Batch973.cert_lt
#print axioms Nock.RedTeam.Batch973.read_row_facts
#print axioms Nock.RedTeam.Batch973.verify_row_facts
