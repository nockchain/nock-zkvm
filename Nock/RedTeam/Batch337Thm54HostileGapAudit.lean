/-
  Nock/RedTeam/Batch337Thm54HostileGapAudit.lean

Sections:
  * §A  constant walk of the proof term of `acceptance_outside_failure_implies_target`
        (`value?
  * §B  field inventory of `OptimizedHistoricalAcceptanceAt` /
        `OptimizedProductionGenuineTargetAt`: which of `Qc`, `Qm`, `c` and which
        package projections each field's type mentions.
  * §C  binder lists of the two spine theorems, the package-vs-fixture scan of their
        binder types, and the three-ring call chain `containment →
        verifierGeneratedTopologyRawContainment_of_slotSemantics →
        verifierGeneratedTopologyRawContainment → accepted_outside_failureUnion`.
  * §D  the acceptance predicate PINS five of the seven coin coordinates to package
        constants at every trace pair (`acceptance_pins_*`), so the false-acceptance
        set injects into `K × K` (`falseAcceptanceSet_card_le_sq`) and the consumed
        probability conjunct follows from the pins alone
        (`pins_alone_imply_consumed_bound`), with a walk showing that proof reaches
        neither `containment` nor any counted event.
  * §F  the honest-side / hostile-side split of `optimizedFullStrictNockVMROM_of_package`,
        by walking each field's provider.

  -- the paper,
  --          1441,1450-1497,1697-1699
-/
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Lean
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.ProductionRoundChronology
import Nock.NockVMROM.Thm54.WalkTilingEvents

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch337

open Lean Meta Elab Command
open Polynomial
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.ProductionP8Containment

/-! ## §A — the constant walk -/

/-- Direct constants of a declaration's value (theorem bodies included). -/
def directOf (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]


def directNaive (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

/-- Transitive constants of a declaration's PROOF TERM, restricted to names under `Nock`.
Named `reachSet` (Mathlib owns `closure`).  Reachability, not dependence: a name in the set is
mentioned somewhere in the proof's transitive body; it is not thereby load-bearing for any one
conjunct. -/
def reachSet (env : Environment) (root : Name)
    (dir : Environment → Name → Array Name := directOf) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := dir env root
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if (`Nock).isPrefixOf c then
      for d in dir env c do
        unless seen.contains d do stack := stack.push d
  return seen



def ROOT : Name :=
  ``OptimizedFullStrictNockVMROMPackage.acceptance_outside_failure_implies_target309
def CONT : Name := ``OptimizedFullStrictNockVMROMPackage.containment
def PROB : Name := ``OptimizedFullStrictNockVMROMPackage.optimizedFalseAcceptance309_probability_le
def OFP : Name := ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

/-- The semantic conjunct's constants. -/
def semanticNames : List Name :=
  [``ProductionP8Containment.GenuineTargetAt, ``ProductionP8Containment.GenuineWitness,
   ``Nock.FieldEmbedding.evalFBy]

/-- Semantic constants that occur only in the TYPE of `GenuineWitness` (a structure has no
value), so a proof-term walk cannot enter them from any root; reported, not asserted. -/
def semanticTypeOnly : List Name :=
  [``P8PublicClaim.HoldsMod, ``TemplateRawJointSoundness.Strategy.FieldTargetAt]

/-- Constants that read the committed compute trace `Qc` (or both traces). -/
def qcReaders : List Name :=
  [``OptimizedFullStrictNockVMROMPackage.computeBaseEnv,
   ``OptimizedFullStrictNockVMROMPackage.hostileRequests,
   ``OptimizedFullStrictNockVMROMPackage.hostileRecords,
   ``OptimizedComputeHostileAccumulator.rowRequests,
   ``OptimizedComputeHostileAccumulator.rowEnv,
   ``OptimizedComputeSemanticRealization.gatherCorrectedFinalTypedEnv]

def spineNames : List Name :=
  [``ServedLookupBridge.verifierGeneratedTopologyRawContainment_of_slotSemantics,
   ``RawSemanticAssembly.verifierGeneratedTopologyRawContainment,
   ``ProductionP8Containment.accepted_outside_failureUnion]

def roundNames : List Name :=
  [``RoundFibred.roundUnion_card_le, ``RoundFibred.StagedAssignment.col_reads]

def report (tag : String) (s : Std.HashSet Name) (names : List Name) : MessageData :=
  let rows := names.map fun n =>
    m!"  {if s.contains n then "PRESENT" else "absent "}  {n}"
  m!"{tag} reach={s.size}\n" ++ MessageData.joinSep rows "\n"

/-! §A.1 — removed at H1.5b Part 2a: the walk asserted that `acceptance_outside_failure_implies_target`
reaches the K-side semantics through `containment` (the provider of the target's `p8` conjunct). -/

/-! ## §B — field inventory -/

/-- Package projections whose presence in a field's type marks it honest-side. -/
def packageMarks : List (Name × String) :=
  [(``OptimizedFullStrictNockVMROMPackage.strategy, "P.strategy"),
   (``OptimizedFullStrictNockVMROMPackage.objects, "P.objects"),
   (``OptimizedFullStrictNockVMROMPackage.OptimizedSameProblemAt,
      "P.OptimizedSameProblemAt (its body reads P.objects, P.optimized.verifier, P.optimized.family)"),
   (``OptimizedFullStrictNockVMROMPackage.q, "P.q"),
   (``OptimizedStrictNockVMROMPackage.sampled, "P.optimized.sampled"),
   (``OptimizedStrictNockVMROMPackage.verifier, "P.optimized.verifier"),
   (``OptimizedStrictNockVMROMPackage.family, "P.optimized.family"),
   (``OptimizedStrictNockVMROMPackage.Λ, "P.optimized.Λ"),
   (``OptimizedStrictNockVMROMPackage.basis, "P.optimized.basis"),
   (``OptimizedStrictNockVMROMPackage.OptimizedSharedMemoryConnective, "P.optimized.SharedMemoryConnective")]

/-- Chip-column readers whose presence marks a field as reading a committed trace. -/
def traceMarks : List (Name × String) :=
  [(``OptimizedFullStrictNockVMROMPackage.computeBaseEnv, "computeBaseEnv Qc"),
   (``OptimizedFullStrictNockVMROMPackage.memorySourceEnv, "memorySourceEnv Qm"),
   (``OptimizedFullStrictNockVMROMPackage.memoryBaseEnv, "memoryBaseEnv Qm"),
   (``OptimizedFullStrictNockVMROMPackage.hostileRecords, "hostileRecords Qc Qm"),
   (``OptimizedFullStrictNockVMROMPackage.hostileRequests, "hostileRequests Qc"),
   (``OptimizedFullStrictNockVMROMPackage.computeChip, "computeChip"),
   (``OptimizedFullStrictNockVMROMPackage.memoryChip, "memoryChip")]

structure FieldRow where
  field : Name
  fvars : List String   -- which of Qc Qm c occur in the field's type
  marks : List String
  deriving Inhabited

def fieldRow (S field : Name) : MetaM FieldRow := do
  let env ← getEnv
  let some proj := getProjFnForField? env S field | throwError m!"no projection {S}.{field}"
  let ci ← getConstInfo proj
  forallTelescope ci.type fun xs body => do
    let mut fv : List String := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (d.userName == `Qc || d.userName == `Qm || d.userName == `c) &&
          body.containsFVar x.fvarId! then
        fv := fv ++ [toString d.userName]
    let consts := body.getUsedConstants
    let mut marks : List String := []
    for (n, lbl) in packageMarks ++ traceMarks do
      if consts.contains n then marks := marks ++ [lbl]
    return ⟨field, fv, marks⟩

def inventory (S : Name) : MetaM (Array FieldRow) := do
  let env ← getEnv
  let fields := getStructureFields env S
  fields.mapM (fieldRow S)

def rowsMsg (rows : Array FieldRow) : MessageData :=
  MessageData.joinSep (rows.toList.map fun r =>
    m!"  {r.field} : mentions {r.fvars} ; {r.marks}") "\n"

/-! §B.1 — the acceptance predicate: exactly `p8` and `same_problem` mention no chip column and
carry `P.strategy` / `P.objects`; `sampled_io_coins` pins `c.2.1` to `P.optimized.sampled` and
reads no column either; the remaining four read `Qc` or `Qm`. -/
run_cmd do
  let rows ← liftTermElabM (inventory ``OptimizedFullStrictNockVMROMPackage.OptimizedHistoricalAcceptanceAt)
  let get (f : Name) : CommandElabM FieldRow := do
    match rows.find? (·.field == f) with
    | some r => pure r
    | none => throwError m!"acceptance has no field {f}"
  let p8 ← get `p8
  unless p8.fvars == ["c"] && p8.marks.contains "P.strategy" do throwError "p8 shape"
  unless (p8.marks.filter (fun m => traceMarks.any (·.2 == m))).isEmpty do throwError "p8 reads a column"
  let sp ← get `same_problem
  unless sp.fvars == ["c"] && sp.marks.any (·.startsWith "P.OptimizedSameProblemAt") do
    throwError "same_problem shape"
  unless (sp.marks.filter (fun m => traceMarks.any (·.2 == m))).isEmpty do throwError "same_problem reads a column"
  let io ← get `sampled_io_coins
  unless io.fvars == ["c"] && io.marks.contains "P.optimized.sampled" do throwError "sampled_io_coins shape"
  unless (io.marks.filter (fun m => traceMarks.any (·.2 == m))).isEmpty do throwError "sampled_io_coins reads a column"
  for f in [`memory_sampled_coins, `memory_intermediate_pole, `memory_satisfies] do
    let r ← get f
    unless r.fvars.contains "Qm" do throwError m!"{f} does not mention Qm"
  let cs ← get `compute_satisfies
  unless cs.fvars == ["Qc"] do throwError "compute_satisfies shape"
  -- no field mentions P.strategy except p8
  for r in rows do
    if r.field != `p8 && r.marks.contains "P.strategy" then throwError m!"{r.field} mentions P.strategy"
  logInfo (m!"B.1 OptimizedHistoricalAcceptanceAt ({rows.size} fields)\n" ++ rowsMsg rows)



/-! ## §C — genericity of the spine -/

def telescope (n : Name) : MetaM (Array (Name × BinderInfo × Expr)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo, l.type)

/-- Names whose appearance in a binder type would make the theorem package- or fixture-scoped. -/
def scopeTraps : List Name :=
  [``OptimizedFullStrictNockVMROMPackage, ``OptimizedStrictNockVMROMPackage,
   `Nock.NockVMROM.Thm54.K97cubic, `Nock.NockVMROM.Thm54.K73cubic,
   `Nock.NockVMROM.Thm54.packageP, `Nock.NockVMROM.Thm54.packageR,
   ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement]

/-- Binders pretty-printed INSIDE the telescope (so names, not `_fvar`s, appear). -/
def telescopePP (n : Name) : MetaM (Array (Name × BinderInfo × Format × Array Name)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      let ty ← instantiateMVars l.type
      pure (l.userName, l.binderInfo, ← ppExpr ty, ty.getUsedConstants)

def printBinders (n : Name) : CommandElabM Unit := do
  let tel ← liftTermElabM (telescopePP n)
  let mut lines : Array MessageData := #[]
  let mut expl : Nat := 0
  let mut hasT := false
  for (nm, bi, fmt, consts) in tel do
    if bi == .default then expl := expl + 1
    for t in scopeTraps do
      if consts.contains t then throwError m!"{n}: binder {nm} mentions scope trap {t}"
    if nm == `T then
      hasT := true
      unless bi == .default do throwError m!"{n}: T is not an explicit binder"
      unless consts.contains ``ProductionP8Containment.ProductionStrategy do
        throwError m!"{n}: T is not a ProductionStrategy"
    let biStr := match bi with
      | .default => "explicit" | .implicit => "implicit"
      | .instImplicit => "instance" | .strictImplicit => "strict"
    lines := lines.push m!"  ({biStr}) {nm} : {fmt}"
  unless hasT do throwError m!"{n}: no binder named T"
  logInfo (m!"C {n}: binders={tel.size} explicit={expl}\n" ++ MessageData.joinSep lines.toList "\n")

run_cmd printBinders ``ProductionP8Containment.accepted_outside_failureUnion
run_cmd printBinders ``ProductionP8Containment.production_jointProbability_falseAcceptance_le

/-! §C.3 — the three-ring chain from the package field to the generic spine, by direct
constants of each body. -/
run_cmd do
  let env ← getEnv
  let step (a b : Name) : CommandElabM Unit := do
    unless (directOf env a).contains b do throwError m!"{a} does not directly use {b}"
  step CONT ``ServedLookupBridge.verifierGeneratedTopologyRawContainment_of_slotSemantics
  step ``ServedLookupBridge.verifierGeneratedTopologyRawContainment_of_slotSemantics
       ``RawSemanticAssembly.verifierGeneratedTopologyRawContainment
  step ``RawSemanticAssembly.verifierGeneratedTopologyRawContainment
       ``ProductionP8Containment.accepted_outside_failureUnion
  -- hop is derived from the two package fields, not assumed
  step ``ServedLookupBridge.verifierGeneratedTopologyRawContainment_of_slotSemantics
       ``ServedLookupBridge.skeletonOperationalCore_of_parts
  logInfo m!"C.3 CHAIN containment → verifierGeneratedTopologyRawContainment_of_slotSemantics → verifierGeneratedTopologyRawContainment → accepted_outside_failureUnion; hop := skeletonOperationalCore_of_parts (recordEquations, slotSemantics)"

/-! ## §D — the acceptance predicate pins five of the seven coordinates -/

section Pins

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  [Fintype F] [DecidableEq F]

/-- `same_problem` pins the NPR seed to the package's honest seed
(`TemplateRawJointSoundness.specializedProblem_seed`). -/
theorem acceptance_pins_seed
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    nprSeed c.1 = P.objects.cfg.challenges.z := by
  have h := congrArg (fun Q : RawProblem F K => Q.cfg.challenges.z)
    hacc.same_problem.specialized_eq_objects
  simpa [TemplateRawJointSoundness.specializedProblem_seed] using h

/-- `same_problem` pins the timestamp base to the package's honest `α`
(`TemplateRawJointSoundness.specializedProblem_tableAlpha`, a `rfl`). -/
theorem acceptance_pins_alphaM
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    alphaM c.1 = P.objects.cfg.challenges.α := by
  have h := congrArg (fun Q : RawProblem F K => Q.cfg.challenges.α)
    hacc.same_problem.specialized_eq_objects
  simpa [TemplateRawJointSoundness.specializedProblem_tableAlpha] using h

/-- `memory_intermediate_pole` pins the tuple's internal pole to the package slot: a challenge is
not a trace column (`memorySourceEnv_inter_pole` is `rfl`). -/
theorem acceptance_pins_interPole
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2.2.2.interPole = P.packageInterPole := by
  have h := hacc.memory_intermediate_pole ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
  rw [P.memorySourceEnv_inter_pole] at h
  exact h.symm

/-- The five pins together: for EVERY trace pair, acceptance leaves only `(αc, γ)` free. -/
theorem acceptance_pins_five
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    nprSeed c.1 = P.objects.cfg.challenges.z ∧
      alphaM c.1 = P.objects.cfg.challenges.α ∧
      c.2.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) ∧
      c.2.2.2.interPole = P.packageInterPole :=
  ⟨acceptance_pins_seed P Qc Qm c hacc, acceptance_pins_alphaM P Qc Qm c hacc,
   hacc.sampled_io_coins, acceptance_pins_interPole P Qc Qm c hacc⟩



end Pins

/-! §D.2 — removed at H1.5b Part 2a: it walked `pins_alone_imply_consumed_bound`, which needs the
pre-2a acceptance's coin pins at the capstone's false-acceptance set. -/

/-! ## §F — honest-side vs hostile-side fields of the capstone -/

/-! §F — For each field of `optimizedFullStrictNockVMROM_of_package`, the provider constant(s) it is
filled from, read off the instance's body: a projection of `P` is honest-side (a compiler-proved
fact about the package); a theorem quantifying over `Qc`/`Qm` is hostile-side. -/
run_cmd do
  let env ← getEnv
  let some ci := env.find? OFP | throwError "no of_package"
  let some v := ci.value? (allowOpaque := true) | throwError "of_package has no value"
  let direct := v.getUsedConstants.toList.filter fun n =>
    (`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage).isPrefixOf n &&
      n != ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement.mk
  -- which of them mention Qc/Qm in their own type
  let mut lines : Array MessageData := #[]
  let mut hostile : Array Name := #[]
  let mut honest : Array Name := #[]
  for n in direct do
    let tel ← liftTermElabM (telescope n)
    let hasQ := tel.any (fun (nm, _, _) => nm == `Qc || nm == `Qm)
    if hasQ then hostile := hostile.push n else honest := honest.push n
    lines := lines.push m!"  {if hasQ then "HOSTILE(∀ Qc Qm)" else "honest-side     "}  {n}"
  unless hostile.contains ROOT do throwError "acceptance_to_target not classified hostile"
  unless hostile.contains PROB do throwError "complete_false_acceptance_bound not classified hostile"
  unless honest.contains CONT do throwError "containment not classified honest-side"
  unless honest.contains ``OptimizedFullStrictNockVMROMPackage.shared_io do throwError "shared_io"
  unless honest.contains ``OptimizedFullStrictNockVMROMPackage.p8_fixedField_falseAcceptance_le do
    throwError "p8_fixed_field_soundness"
  logInfo (m!"F providers of optimizedFullStrictNockVMROM_of_package: {direct.length} (hostile={hostile.size}, honest-side={honest.size})\n"
    ++ MessageData.joinSep lines.toList "\n")

end Nock.RedTeam.Batch337

#print axioms Nock.RedTeam.Batch337.acceptance_pins_five
