/-
  Nock/RedTeam/Batch905Thm54R4HonestPremiseCensus.lean

  Additive; nothing consumes this.

  `r4_bridge_at` takes
  (after the package, the tuple and the two traces)

  * `hacc  : DeployedAcceptanceAt P c Qc Qm`      -- two RAP conjuncts at the family chips;
  * `hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm)`;
  * `hio   : FamilyIOGood P c Qc Qm`              -- `c.2.1 ∉ IOFailureEvent` at the family records;
  * `hrb   : 3 * compRows < ringChar K ∧ memRows < ringChar K`;
  * `hb    : Batch823.CertBitsBoolean P c Qc`;
  * `h1    : coord P.optimized.basis 1 0 ≠ 0`.

  `r4_path_valid_at` adds

  * `hU : ∀ r ∈ Icc 1 kMem, UniqueExponents (decodedMTreeOfEnvs...)`;
  * `hA : ∀ e, decodedShift envsC e ≤ formRN K - 1`.

  `R4Premises` is exactly that conjunction, and `r4_path_valid_of_premises` is
  `r4_path_valid_at` restated on it, so "the premise set holds at an instance" is one `Prop`.
  Acceptance is stated at `DeployedAcceptanceAt` (two `RAP.SatisfiesWithPreprocessing` conjuncts at
  `computeChipAt c` / `memoryChipAt c`), so the file builds unchanged after the 2a merge.
-/
import Nock.RedTeam.Batch824Thm54R4Bridge
import Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch905

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FormRBridge
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch824

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- **The full hypothesis set of `r4_bridge_at` and `r4_path_valid_at`**, in the order of their
signatures.  Nothing is added and nothing is dropped. -/
structure R4Premises : Prop where
  hacc : DeployedAcceptanceAt P c Qc Qm
  hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm)
  hio : FamilyIOGood P c Qc Qm
  hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K
  hb : Batch823.CertBitsBoolean P c Qc
  h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0
  hU : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
    UniqueExponents (decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
      P.optimized.family.problem.cfg.kMem r)
  hA : ∀ e, decodedShift (envsCR P c Qc) e ≤ FormRAxisEvent.formRN K - 1

/-- **`r4_path_valid_at` on the bundle**: the instantiated conclusion. -/
theorem r4_path_valid_of_premises (H : R4Premises P c Qc Qm) :
    ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      let t := decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r
      (∀ e, readCount e t = verifyCount e t) ∧
        ∀ e, Paired e t →
          Padding (FormRAxisEvent.formRN K) (decodedShift (envsCR P c Qc) e)
              (decodedBits (envsCR P c Qc) e) ∧
            ∃ q, Batch554.rpaths e t = [q] ∧
              Batch554.vpaths e t =
                [q ++ Batch554.bitsOf (decodedShift (envsCR P c Qc) e)
                  (decodedBits (envsCR P c Qc) e)] :=
  r4_path_valid_at P c Qc Qm H.hacc H.hgood H.hio H.hrb H.hb H.h1 H.hU H.hA

end

end Nock.RedTeam.Batch905

#print axioms Nock.RedTeam.Batch905.r4_path_valid_of_premises
