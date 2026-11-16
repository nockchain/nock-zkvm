/-
  Nock/RedTeam/Batch592Thm54SpecializeEncodeConsumers.lean

  Instruments (elaboration-time; a false assertion FAILS THE BUILD): `Batch587.closureOf` (type +
  value, theorem bodies included, `value? (allowOpaque := true)`), `Batch587.mentionsAxis`
  (`MemRec.axis` as constant or `Expr.proj _ 2`), and here `mentionsPlaceholder`
  (`MemoryRowTemplate.placeholder` as constant or `Expr.proj _ 1`) and `mentionsConst`.
  Auxiliary `._proof_` / `.eq_` / `match_` / `._mutual` constants are folded into their parents.
  Positive control: `templateAxisTree` (the S1 object) is found as a placeholder-axis reader.
  Negative control: the H1 wrap names (`wrapMemoryLabel`, `specializeMemRec_memExponent`) are
  found absent from the capstone closure.

  What is compiled here:
  * §1 **The nine direct readers of a template placeholder's axis** in the closure of
    `nockCompiles_zmod` (exact list, `run_cmd`); five of them also read `MemoryRowTemplate.specialize`
    — those five are the ones that assume template = exec on `mem.axis`.
  * §2 **Membership of the indirect consumers** (`run_cmd`): `specializedAxisValidity_of_accepts`,
    `verifierGuardedRootAlphas`, `rootPolynomial_of_exactMemoryAxisValidity`,
    `ExactServedMemoryTrace`, `ExactMemoryAxisValidity`, `exactAxisTree`, `RootAxisBoundaryAt`,
    `MemoryTimestampSpecializesAt`, `bindMemRec_specialize_active` are IN; the honest generic
    boundary `honest_templateAxisPolynomial_eval` and the H1 wrap are OUT.
  * §3 **What breaks under S2, concretely** (live concrete axis-3 template, `p = 73`):
    `specialize_memory_axis_of_active`'s S2 twin is false (`s2_specialize_axis_ne`), and the
    exec-level accounting that `ofNTree_specialize_toMTree` / `specialized_countsP_eval` transport
    no longer agrees with the template (`exec_level_accounting_breaks`).
-/
import Nock.RedTeam.Batch591Thm54SpecializeEncodeBinding
import Nock.NockVMROM.Thm54.GenericHonestPackage
import Nock.NockVMROM.Thm54.BuildableAxisWitness

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch592

open Lean Meta Elab Command
open Nock.RedTeam.Batch587

/-! ## §0 Instruments -/

def mentionsConst (e : Expr) (n : Name) : Bool :=
  (e.find? fun x => match x with
    | .const m _ => m == n
    | _ => false).isSome

def mentionsProj (e : Expr) (s : Name) (i : Nat) : Bool :=
  (e.find? fun x => match x with
    | .proj s' i' _ => s' == s && i' == i
    | _ => false).isSome

def ownExprs (env : Environment) (n : Name) : List Expr :=
  match env.find? n with
  | none => []
  | some ci => [ci.type, (ci.value? (allowOpaque := true)).getD (.sort .zero)]

def mentionsPlaceholder (e : Expr) : Bool :=
  mentionsConst e ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.placeholder ||
  mentionsProj e ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate 1

def mentionsMemSpecialize (e : Expr) : Bool :=
  mentionsConst e ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specialize

/-- Auxiliary constants folded into their parents. -/
def fold (n : Name) : Bool :=
  let s := n.toString
  (s.splitOn "._").length > 1 || (s.splitOn ".eq_").length > 1 || (s.splitOn "match_").length > 1
    || (s.splitOn "proof_").length > 1

/-! ## §1 Direct readers of a template placeholder's axis -/

/-- The nine capstone-closure constants whose own type/value reads both a memory template's
placeholder and `MemRec.axis` (measured; asserted exactly below). -/
def placeholderAxisReaders : List Name :=
  [``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.bindsRow_specialize,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.ofNTree_specialize_toMTree,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree_reindex,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_axis_of_active,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_ts_of_active,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisTree,
   ``Nock.NockVMROM.Thm54.TemplateAxisStructure.recoveredAxisTree_eq_reindexAxisTree]

/-- The five of them that also read `MemoryRowTemplate.specialize`: these assume template = exec
on `mem` (all break or must be restated under S2). -/
def templateEqExecReaders : List Name :=
  [``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.bindsRow_specialize,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.ofNTree_specialize_toMTree,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_axis_of_active,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_ts_of_active]

def sortNames (xs : Array Name) : List Name := (xs.qsort (·.toString < ·.toString)).toList

def post28thPlaceholderDropped : List Name :=
  [``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree_reindex]

def post28thPlaceholderAdded : List Name :=
  [``Nock.NockVMROM.Thm54.HonestCommitment.memory_specializeA_placeholder_eq,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.recoveredAxisTree_reindex_bin,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specialize_mem_inactive,
   ``Nock.RedTeam.Batch973.specialize_wrapR0_eq_self]

/-- No longer read
`MemoryRowTemplate.specialize` together with `MemRec.axis` (the first left the closure; the other
three are still in it and now go through the a-bearing `specializeA`). -/
def post28thTemplateEqExecDropped : List Name :=
  [``Nock.NockVMROM.Thm54.HonestCommitment.memory_specialize_placeholder_eq,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.ofNTree_specialize_toMTree,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_axis_of_active,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialize_memory_ts_of_active]

def post28thTemplateEqExecAdded : List Name :=
  [``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specialize_mem_inactive,
   ``Nock.RedTeam.Batch973.specialize_wrapR0_eq_self, ``Nock.RedTeam.Batch974.row_identity_ev]

def post30thPlaceholderAdded : List Name :=
  [``Nock.NockVMROM.Thm54.FormRAxisEvent.certAxisAt_active,
   ``Nock.NockVMROM.Thm54.FormRAxisEvent.templateRowCertAxis]

def post28thList (pre dropped added : List Name) : List Name :=
  pre.filter (fun n => !dropped.contains n) ++ added

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstoneName
  for n in post28thPlaceholderDropped do
    unless placeholderAxisReaders.contains n do throwError m!"drift list: {n} not a pre-28th reader"
    if cap.contains n then throwError m!"{n} is back in the capstone closure (post-28th drift)"
  for n in post28thTemplateEqExecDropped do
    unless templateEqExecReaders.contains n do throwError m!"drift list: {n} not a pre-28th reader"
  let mut a : Array Name := #[]
  let mut b : Array Name := #[]
  for n in cap.toList do
    if fold n then continue
    let es := ownExprs env n
    let ax := es.any mentionsAxis
    if ax && es.any mentionsPlaceholder then a := a.push n
    if ax && es.any mentionsMemSpecialize then b := b.push n
  for n in post30thPlaceholderAdded do
    if cap.contains n then throwError m!"{n} is still in the capstone closure (post-32nd drift)"
  let aPost := post28thList placeholderAxisReaders post28thPlaceholderDropped
    (post28thPlaceholderAdded ++
      [``Nock.NockVMROM.Thm54.PartAB0.axisProj_lblMR0_congr, ``Nock.NockVMROM.Thm54.PartAB0.axisProj,
       ``Nock.NockVMROM.Thm54.PartAB0.axisTree_axisProj,
       ``Nock.NockVMROM.Thm54.P8EventEv.templateAxisTree_mapNTree])
  let bPost := post28thList templateEqExecReaders post28thTemplateEqExecDropped post28thTemplateEqExecAdded
  unless sortNames a == sortNames aPost.toArray do
    throwError m!"placeholder-axis readers changed: {sortNames a}"
  unless sortNames b == sortNames bPost.toArray do
    throwError m!"template=exec readers changed: {sortNames b}"
  -- positive control: the S1 object itself is a reader
  unless a.contains ``Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisTree do
    throwError "control: templateAxisTree not found"

/-! ## §2 Indirect consumers: closure membership -/

def inCapstone : List Name :=
  [``Nock.NockVMROM.Thm54.ProductionP8Containment.specializedAxisValidity_of_accepts,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.verifierGuardedRootAlphas,
   ``Nock.NockVMROM.Thm54.BuildableAxisWitness.rootPolynomial_of_exactMemoryAxisValidity,
   ``Nock.NockVMROM.Thm54.BuildableAxisWitness.buildableMemoryProductionAssignment,
   ``Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace,
   ``Nock.NockVMROM.Thm54.ExactMemoryAxisValidity,
   ``Nock.NockVMROM.Thm54.exactAxisTree,
   ``Nock.NockVMROM.Thm54.TemplateAxisStructure.exactAxisTree_specialize,
   ``Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier.exactAxisStructuralRefinement_of_checks,
   ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.RootAxisBoundaryAt,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryTimestampSpecializesAt,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ComputeRowTemplate.bindMemRec_specialize_active,
   ``Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedProblem]

def post28thLeftCapstone : List Name :=
  [``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ComputeRowTemplate.bindMemRec_specialize_active]

def offCapstone : List Name :=
  [``Nock.NockVMROM.Thm54.GenericHonestPackage.honest_templateAxisPolynomial_eval,
   ``Nock.NockVMROM.Thm54.GenericHonestPackage.packageOf_fibre_root_axis_boundary,
   ``Nock.NockVMROM.Thm54.TemplateAxisCounting.specialized_countsP_eval,
   ``Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specializes,
   ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.wrapMemoryLabel,
   ``Nock.NockVMROM.Thm54.WrapMemoryConjuncts.specializeMemRec_memExponent]

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstoneName
  for n in inCapstone ++ offCapstone do
    unless env.contains n do throwError m!"{n} does not exist"
  for n in post28thLeftCapstone do
    unless inCapstone.contains n do throwError m!"drift list: {n} not in inCapstone"
  for n in inCapstone do
    if post28thLeftCapstone.contains n then
      if cap.contains n then throwError m!"{n} is back in the capstone closure (post-28th drift)"
    else
      unless cap.contains n do throwError m!"{n} NOT in the capstone closure"
  for n in offCapstone do
    if cap.contains n then throwError m!"{n} IS in the capstone closure"
  let sv := ownExprs env ``Nock.NockVMROM.Thm54.ProductionP8Containment.specializedAxisValidity_of_accepts
  -- live's soundness use of the template boundary reads it...
  unless sv.any (mentionsConst · ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.RootAxisBoundaryAt) do
    throwError "specializedAxisValidity_of_accepts does not read RootAxisBoundaryAt"
  -- ... and concludes EXEC-level validity
  unless sv.any (mentionsConst · ``Nock.NockVMROM.Thm54.ExactMemoryAxisValidity) do
    throwError "specializedAxisValidity_of_accepts does not conclude ExactMemoryAxisValidity"

/-! ## §3 What breaks under S2, concretely -/

section Concrete

open Nock Nock.Walk Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.RedTeam.Batch588 Nock.RedTeam.Batch591
open AxisBatching AxisBatching.MTree

/-- **`specialize_memory_axis_of_active` has no S2 twin.**  On live's concrete verify template
(placeholder axis `3`), the S2 exec row's axis slot is `T = formRT 2 3 = 2 ≠ 3`. -/
theorem s2_specialize_axis_ne (z α : K73cubic) :
    (s2Specialize 2 α (verifyRowTemplate z)).row.2.2.mem.axis ≠
      (verifyRowTemplate z).placeholder.2.2.mem.axis := by
  rw [(concrete_s2_row z 2 α).1]
  have hs : LcertShift 3 = 1 := by decide
  have hax : (verifyRowTemplate z).placeholder.2.2.mem.axis = 3 := by
    simp [verifyRowTemplate, verifyPubA, requestRecord]
  rw [hax]
  simp only [LformRT, hs, pow_one]
  intro h
  have : ((1 : ℕ) : K73cubic) = 0 := by push_cast; linear_combination -h
  exact SetEq.Lcast_ne_zero (p := 73) (k := 1) (by norm_num) (by norm_num) this

/-- **Exec-level accounting no longer agrees with the template.**  The 2-adic boundary of the
template (a-bearing, S1) vanishes at the honest `α = 4`; the same tree read off the S2 exec row
(axis slot `T`) does not.  This is the content `ofNTree_specialize_toMTree` /
`specialized_countsP_eval` / `rootPolynomial_of_exactMemoryAxisValidity` transport between, so
under S2 they must be restated against the template (or an a-bearing exec), not the exec. -/
theorem exec_level_accounting_breaks (z : K73cubic) :
    (countsP_bin (TemplateAxisCounting.templateAxisTree (readTemplateTree z))).eval honestAlpha = 0 ∧
      (countsP_bin (.read 1 (.decompose .halt
        (.verify 1 (s2Specialize 2 honestAlpha (verifyRowTemplate z)).row.2.2.mem.axis .halt)))
        : K73cubic[X]).eval honestAlpha ≠ 0 := by
  refine ⟨s1_concrete_boundary z honestAlpha, ?_⟩
  rw [(concrete_s2_row z 2 honestAlpha).1, ← concrete_templateAxisTree z]
  exact (rowlevel_concrete_boundary_fails z).2.2

end Concrete

end Nock.RedTeam.Batch592

#print axioms Nock.RedTeam.Batch592.s2_specialize_axis_ne
#print axioms Nock.RedTeam.Batch592.exec_level_accounting_breaks
