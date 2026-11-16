/-
  Nock/NockVMROM/Thm54/UniqueExponentsBridge.lean

  §A is env-generic and premise-free beyond an exponent-injectivity hypothesis per state class
  (it holds at every env tuple): the BFS inversion visits each row at most once
  (`DecodedLambdaEvent.child_parent_unique` / `reach_disjoint`), so a tree has two nodes of one
  class at exponent `e` only if two distinct rows of that class carry `e`.

  §B discharges the two injectivity hypotheses at the family chips:
  * `verify_child` rows (selectors one-hot by `bsum4`) are matched to `read_root` rows by the
    `intermediate` LogUp (`paired_records_of_rowsBound_at`); the read records are nodup, hence so
    are the verify records, and two verify rows with one exponent share a read partner.

  `hb1 : coord P.optimized.basis (1 : K) 0 ≠ 0`.  `readRootVerGate` pins only coordinate `0` of
  `ver` to coordinate `0` of `1`; at a basis whose `0`-th coordinate of `1` vanishes the gate is
  vacuous and a hostile `read_root` row may carry `ver = 0`, outside route B.  The compiler basis
  extends `{1}` (`TraceGen.compilerBasis_zero`, `b 0 = 1`), so `hb1` holds at every generated
  package; `Batch521.readRoot_sel_implies_ver1` carries the same hypothesis.

  No `S`, no
  `same_problem`, no `p8`, no `Vmem` / `interV` (reach receipt: `Batch845`).
-/
import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.P8Core.UniqueExponentsBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nock.NockVMROM.Thm54.UniqueExponentsBridge

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch575 (UniqueExponents)

noncomputable section

/-! ## A. Env-generic: an exponent-injective state class has at most one node per exponent -/

section Generic

variable {F K : Type} [Field F] [Field K] [DecidableEq F] {M : ℕ}
variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (kroots : ℕ)

end Generic

/-! ## B. The two injectivity hypotheses at the family chips -/

section Family

open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open DeployedChipFamily
open FamilyComputeRows
open FamilyMemoryRows
open FamilyIOChain

open Module

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

section Accepted

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)

include hacc hgood hio hrb hb1

/-- **THE `UniqueExponents` BRIDGE (family envs).** -/
theorem uniqueExponents_decoded_at (kroots i : ℕ) :
    UniqueExponents (decodedMTreeOfEnvs (memEnvK P c Qm) (memEnvF P c Qm) kroots i) :=
  uniqueExponents_of_expInj _ _ kroots
    (expInj_read_at P c Qc Qm hacc hgood hio hrb hb1)
    (expInj_verify_at P c Qc Qm hacc hgood hio hrb hb1) i

end Accepted

end Family

end

end Nock.NockVMROM.Thm54.UniqueExponentsBridge
