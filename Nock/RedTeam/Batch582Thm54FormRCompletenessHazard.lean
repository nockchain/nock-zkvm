/-
  Nock/RedTeam/Batch582Thm54FormRCompletenessHazard.lean

  The `OW` completeness hazard
  against the landed objects.

  2. **Consumers of `Nested` / `ReadVerifyNested` still on the Form R path after `PC`**, MEASURED:
     the declarations in the transitive type + value closure (theorem bodies included,
     `value? (allowOpaque := true)`, Batch593's `closureOf`) of `nockCompiles_zmod` and of
     `optimizedFullStrictNockVMROM_of_package` whose own type or value names
     `AxisBridge.ReadVerifyNested` or `AxisBatching.MTree.Nested`.  `nockCompiles_zmod`: 28;
     `of_package`: 22 (a subset).  The `run_cmd` below re-measures and FAILS THE BUILD if either
     set moves.  Positive control: both targets are in both closures, and the instrument finds
     `alphaFreeAxisStructureCheck_eq_true_iff`, whose statement names `ReadVerifyNested`.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch575Thm54FormRMtree
import Nock.RedTeam.Batch593Thm54FormRAxisConsumers
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch582

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.RedTeam.Batch575

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem cert_axis1 :
    certShiftOf (fun _ => 1) = axis1 ∧ certBitsOf (fun _ => 1) = axis1bits := by
  refine ⟨funext fun _ => by simp [certShiftOf, axis1, MemoryTable.formRCertShift, Nat.size_one],
    funext fun _ => funext fun _ => ?_⟩
  simp [certBitsOf, axis1bits, MemoryTable.formRCertBit, MemoryTable.formRCertShift, Nat.size_one]

/-- `s2FailTree` satisfies the landed Form R root identity (path equation). -/
theorem s2_passes_formR (e : ℕ) (a : K) :
    FormRRootIdentity (fun _ => 1) (s2FailTree e a) := by
  simpa [FormRRootIdentity, formRPolyOfCert, cert_axis1.1, cert_axis1.2] using
    s2Fail_counts (K := K) (formRN K) e a

theorem s2_passes_formR_structure (e : ℕ) (a : K) :
    formRRootStructureCheck (fun _ => 1) (s2FailTree e a) :=
  ⟨s2Fail_unique e a, s2_passes_formR e a⟩

theorem s2_fails_ancestryScan (e : ℕ) (a : K) :
    (ancestryScan (s2FailTree e a)).accepts = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  exact (s2Fail_not_nested e a).2 ((ancestryScan_accepts_iff _).mp htrue)

theorem s2_fails_readVerifyNested (e : ℕ) (a : K) :
    ¬ ReadVerifyNested (s2FailTree e a) :=
  (s2Fail_not_nested e a).2

/-- OW completeness hazard at the landed certificate: Form R accepts, ancestry rejects. -/
theorem s2_formR_vs_ancestry (e : ℕ) (a : K) :
    FormRRootIdentity (fun _ => 1) (s2FailTree e a) ∧
      (ancestryScan (s2FailTree e a)).accepts = false ∧
      ¬ ReadVerifyNested (s2FailTree e a) :=
  ⟨s2_passes_formR e a, s2_fails_ancestryScan e a, s2_fails_readVerifyNested e a⟩

/-! ## The `Nested` consumers on the Form R path (measured) -/

open Lean Meta Elab Command

def nestedTargets : List Name := [``Nock.AxisBridge.ReadVerifyNested, ``Nock.AxisBatching.MTree.Nested]

def namesNested (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    (ci.type.getUsedConstants ++ v.getUsedConstants).any (nestedTargets.contains ·)

/-- Recorded: direct `Nested` / `ReadVerifyNested` users in the closure of `nockCompiles_zmod`. -/
def nestedConsumersZmod : List Name :=
  [``Nock.AxisBatching.MTree.axis_batching_sound, ``Nock.AxisBatching.MTree.ccoef_full,
   ``Nock.AxisBatching.MTree.coeff_eq, ``Nock.AxisBridge.countsP_zero_of_exactMemoryAxisValidity,
   ``Nock.AxisBridge.nested_of_readVerifyNested, ``Nock.AxisBridge.nested_of_seedWalk,
   ``Nock.AxisBridge.rc_le_vc_of_rvn, ``Nock.AxisBridge.seedWalk_of_nounShape,
   ``Nock.AxisBridge.seedWalk_of_readVerifyNested, ``Nock.NockVMROM.Thm54.ExactMemoryAncestry,
   ``Nock.NockVMROM.Thm54.OptimizedMemorySameExecution.MemoryProductionAssignment.axis_eq_relaxis_of_used,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.AlphaFreeAxisStructure.ancestry,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.AlphaFreeAxisStructure.mk,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeRootStructureCheck_eq_true_iff,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.ancestryScan_accepts_iff,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_checks,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.readVerifyNestedCheck_eq_true_iff,
   `Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.readVerifyNestedCheck_eq_true_iff._simp_1,
   ``Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readVerifyNested,
   ``Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity,
   ``Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.readVerifyNested,
   ``Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.spec,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.TemplateAxisBadWitness,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.recovered_badWitness_of_specialized_bad,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisPolynomial_ne_zero_of_recovered_bad,
   ``Nock.NockVMROM.Thm54.TemplateAxisStructure.readVerifyNested_reindexAxisTree]

/-- The zmod list has one more entry, a private lemma
(`ServedMemoryTrace.nested_of_event_counts_zero`), counted by name suffix in the guard. -/
def nestedPrivateSuffix : String := "nested_of_event_counts_zero"

/-- Recorded: the subset also in the closure of `of_package` (22 names). -/
def nestedConsumersOfPackage : List Name :=
  nestedConsumersZmod.filter fun n =>
    !(n == ``Nock.AxisBridge.countsP_zero_of_exactMemoryAxisValidity ||
      n == ``Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace.readVerifyNested ||
      n == ``Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.axisValidity ||
      n == ``Nock.NockVMROM.Thm54.ServedMemoryTrace.ServiceWalk.readVerifyNested ||
      n == ``Nock.NockVMROM.Thm54.ServedMemoryTrace.VerifyRoute.spec)

theorem nestedConsumers_counts :
    nestedConsumersZmod.length + 1 = 28 ∧ nestedConsumersOfPackage.length = 22 := by
  decide

-- The guard: re-measure both closures; fail the build on any drift.
run_cmd do
  let env ← getEnv
  let check (root : Name) (expected : List Name) (privates : Nat) : CommandElabM Unit := do
    let cl := Nock.RedTeam.Batch593.closureOf env root
    unless nestedTargets.all cl.contains do
      throwError "Batch582: positive control failed, a target is not in the closure of {root}"
    let hits := cl.toList.filter (namesNested env)
    let pub := hits.filter fun n => !isPrivateName n
    let priv := hits.filter fun n => isPrivateName n
    unless pub.length == expected.length && expected.all pub.contains do
      throwError "Batch582: the Nested consumer set of {root} moved: {pub}"
    unless priv.length == privates do
      throwError "Batch582: private Nested users of {root} moved: {priv}"
    unless priv.all (fun n => (n.toString.splitOn nestedPrivateSuffix).length > 1) do
      throwError "Batch582: unexpected private Nested user of {root}: {priv}"
  check ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod nestedConsumersZmod 1
  check ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
    nestedConsumersOfPackage 0
  unless namesNested env
      ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff do
    throwError "Batch582: positive control failed"

end Nock.RedTeam.Batch582

#print axioms Nock.RedTeam.Batch582.s2_formR_vs_ancestry
#print axioms Nock.RedTeam.Batch582.s2_passes_formR_structure
