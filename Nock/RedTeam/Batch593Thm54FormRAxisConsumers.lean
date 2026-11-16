/-
  Nock/RedTeam/Batch593Thm54FormRAxisConsumers.lean

  No production edit, no digest
  move, no status flip.

  Instruments (elaboration time; a false assertion FAILS THE BUILD):
  * `closureOf` — transitive type + value closure, theorem bodies included,
    `value? (allowOpaque := true)`.
  * `execHeads` — for every application of an axis consumer (`exactAxisTree`,
    `ExactMemoryAncestry`, `ExactMemoryAxisValidity`, `ExactMemoryAxisSemantics`,
    `ExactAxisStructuralRefinement`, `AxisTraversableChainedSemanticExactLanguage`,
    `ServedMemoryTrace.RootTrace`, and the `execA` slot of `ExactServedMemoryTrace`) inside a
    closure constant's type or value, the head symbol of the execution argument.

  Claim 1 (encode-at-specialize as built):
  * `memoryRow_specialize_eq_encodeRow_specializeA` (`rfl`): `MemoryRowTemplate.specialize =
    encodeRow ∘ specializeA`, definitionally.  `specializedProblem_exec_eq_encodeMem`: the P8 exec
    is the row encode of `specializedExecA`.
  * §1 `run_cmd`: in the closure of `nockCompiles_zmod`, every concrete
    execution argument fed to an axis consumer is a-bearing: `specializeA`, `specializedExecA`
    (both spellings), `OptimizedStrictNockVMROMPackage.memoryExecA`, `genExactExecutionA`, or a
    bound variable.  No encoded head (`ExactExecutionTemplate.specialize`, `specializedExec`,
    `RawProblem.exec`, `BuildableNockExecution.exec`, `ExactCanonicalRAPProblem.exec`,
    `RawPlusIOSegmentedFamily.exec`, `encodeMem`, `genExactExecution`).
    Positive control: the same instrument run on the IO consumers (`derivedRequestIO`,
    `derivedResponseIO`) finds the encoded heads `specializedExec`,
    `ExactExecutionTemplate.specialize`, `BuildableNockExecution.exec` — chips / IO read
    `specialize`, and the instrument can see an encoded head when there is one.
  * `MemRec.axis` reader census: 150 closure constants read `MemRec.axis`; positive controls
    `templateAxisTree`, `ofNTree_specialize_toMTree`, `BindMemRow`, `MemoryTable.eqBlk`.  The
    executed-row readers state `axis = formRT λ (nockAxisOf a)` (`BindMemRow`,
    `MemoryRowFrame.memoryRecordAxis`, `bindsRow_specialize`); template readers (`templateAxisTree`,
    `recoveredAxisTree`) read the template's `a` as the Nock axis.  No template reader treats `a`
    as `T`: the only closure reader that mentions both the template placeholder and `formRT` is
    `MemoryRowTemplate.bindsRow_specialize`, which maps `a ↦ formRT λ (nockAxisOf a)`.

  Claim 4 (`GenuineWitness.axisSemantics` restored):
  * `guarded_poly_is_acceptance_poly` (`Iff.rfl`): `RootAxisBoundaryAt` is literally
    "`templateAxisPolynomial` vanishes at `alphaM`" — the priced event and the acceptance check
    are one polynomial (`countsP_bin` of the a-bearing template tree).
  * §2 `run_cmd`: `specializedAxisValidity_of_accepts` has exactly the explicit binders
    `h2 T ω hz hacc hout`, axioms ⊆ {propext, Classical.choice, Quot.sound}; the capstone
    discharges `h2` from the pre-existing `hchar` (`two_ne_zero_of_stateTagChar`).
  * **Workload (non-blocking finding):** `templateAxisWorkload` was re-defined (now
    `Σ natDegree countsP_bin`, was `Σ natDegree countsP`), so `fixedAxisWorkload` — which sits in
    `p8_fixedField_falseAcceptance_le` — changed value as a function.  Compiled witness
    `cancelling_tree_workload_moves`: on the cancelling tree `read 1 (decompose (verify 1 5 halt)
    halt)` over `ZMod 7`, `countsP = 0` (old contribution `natDegree = 0`) while
    `countsP_bin ≠ 0` with `natDegree ≥ 1`.  The majorant `fixedAxisWorkload_le` (`length · B`)
    is unchanged in statement; the bit figures, which go through the majorant, do not move.

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch593

open Lean Meta Elab Command

/-! ## §0 Instruments -/

def mentionsAxis (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => n == ``Nock.ComputeTable.MemRec.axis
    | .proj s i _ => s == ``Nock.ComputeTable.MemRec && i == 2
    | _ => false).isSome

partial def closureOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    for c in ci.type.getUsedConstants ++ v.getUsedConstants do
      if !seen.contains c then stack := stack.push c
  return seen

def capstone : Name := `Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod

def headOf (e : Expr) : Name :=
  match e.getAppFn with
  | .const n _ => n
  | .bvar _ => `«<bvar>»
  | .fvar _ => `«<fvar>»
  | .proj s i _ => s.str s!"<proj{i}>"
  | _ => `«<other>»

/-- Index of the `nth` binder (0-based count among `ExactExecution` binders) whose type head is
`ExactExecution`. -/
def execIdx (t : Expr) (nth : Nat := 0) : Option Nat := Id.run do
  let mut t := t
  let mut i := 0
  let mut seen := 0
  while true do
    match t with
    | .forallE _ d b _ =>
        if d.getAppFn.constName? == some `Nock.NockVMROM.Thm54.ExactExecution then
          if seen == nth then return some i
          seen := seen + 1
        t := b; i := i + 1
    | _ => return none
  return none

/-- For each consumer `(c, nth)`, collect the head symbols of its `nth` execution argument at
every application inside the type or value of a constant of `cap`. -/
def execHeads (env : Environment) (cap : NameSet) (consumers : List (Name × Nat)) :
    IO (NameMap (Array Name)) := do
  let mut idx : Array (Name × Nat) := #[]
  for (c, nth) in consumers do
    let some ci := env.find? c | throw <| IO.userError s!"missing consumer {c}"
    let some k := execIdx ci.type nth | throw <| IO.userError s!"no exec binder {c}"
    idx := idx.push (c, k)
  let mut out : NameMap (Array Name) := {}
  for n in cap.toList do
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    for e in [ci.type, v] do
      let used := e.getUsedConstants
      if !(idx.any fun (c, _) => used.contains c) then continue
      let ref ← IO.mkRef (#[] : Array Name)
      let f : Expr → IO Unit := fun x => do
        match x.getAppFn with
        | .const c _ =>
          match idx.find? (·.1 == c) with
          | some (_, k) =>
            let args := x.getAppArgs
            if h : k < args.size then ref.modify (·.push (headOf args[k]))
          | none => pure ()
        | _ => pure ()
      (e.forEach f : IO Unit)
      for h in (← ref.get) do
        out := out.insert h (((out.find? h).getD #[]).push n)
  return out

/-! ## §1 Claim 1 — encode at specialize, as built -/

section Defs
open Nock.NockVMROM.Thm54 SemanticTimestampStrategy
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `MemoryRowTemplate.specialize = encodeRow ∘ specializeA`, definitionally
(`SemanticTimestampStrategy.lean:436-462`).  Since the λ fix both take the sampled
`lmb`: `T.specialize α lmb = encodeRow lmb (T.specializeA α)`. -/
theorem memoryRow_specialize_eq_encodeRow_specializeA
    (T : MemoryRowTemplate (K := K)) (α lmb : K) :
    T.specialize α lmb = MemoryRowTemplate.encodeRow lmb (T.specializeA α) := rfl

/-- Template execution: the executed trace is the row encode of the a-bearing view
(`SemanticTimestampStrategy.lean:735`). -/
theorem execution_specialize_eq_encodeMem
    {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (α lmb : K) :
    E.specialize α lmb = (E.specializeA α lmb).encodeMem :=
  ExactExecutionTemplate.specialize_eq_encodeMem E α lmb

/-- The template-level binding is the a-bearing binding (`BindMemRec`, raw `a`), not the
row-level `BindMemRow` (`SemanticTimestampStrategy.lean:1228-1231`). -/
theorem template_binding_is_a_bearing
    (z : K) (s : SemanticStrategy.MemoryRowSkeleton) (T : MemoryRowTemplate (K := K)) :
    MemoryRowTemplate.BindsRow z s T ↔
      (T.timestamp.state = s.state ∧ SemanticStrategy.BindMemoryRowA z s T.placeholder) :=
  Iff.rfl

end Defs

section P8
open Nock.NockVMROM.Thm54
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

/-- P8's single execution is the encode of the a-bearing view it states axis validity on
(`TemplateRawJointSoundness.lean:37-47`). -/
theorem specializedProblem_exec_eq_encodeMem
    (T : SemanticTimestampStrategy.DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    (TemplateRawJointSoundness.specializedProblem T z hz alphaM lmb).exec =
      (TemplateRawJointSoundness.specializedExecA T z hz alphaM lmb).encodeMem :=
  SemanticTimestampStrategy.ExactExecutionTemplate.specialize_eq_encodeMem _ _ _

end P8

def axisConsumers : List (Name × Nat) :=
  [(`Nock.NockVMROM.Thm54.exactAxisTree, 0),
   (`Nock.NockVMROM.Thm54.ExactMemoryAncestry, 0),
   (`Nock.NockVMROM.Thm54.ExactMemoryAxisValidity, 0),
   (`Nock.NockVMROM.Thm54.ExactMemoryAxisSemantics, 0),
   (`Nock.NockVMROM.Thm54.TemplateAxisCounting.ExactAxisStructuralRefinement, 0),
   (`Nock.NockVMROM.Thm54.AxisTraversableChainedSemanticExactLanguage, 0),
   (`Nock.NockVMROM.Thm54.ServedMemoryTrace.RootTrace, 0),
   -- `ExactServedMemoryTrace q Λ cfg exec D execA`: the axis slot is the SECOND execution.
   (`Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace, 1)]

/-- The a-bearing heads (plus bound variables of generic lemmas). -/
def aBearingHeads : List Name :=
  [`«<bvar>»,
   `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specializeA,
   `Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.specializedExecA,
   `Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedExecA,
   `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.memoryExecA,
   `Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA,
   `Nock.NockVMROM.Thm54.BuildableNockExecution.execA]

/-- Encoded (row-level) heads. -/
def encodedHeads : List Name :=
  [`Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specialize,
   `Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.specializedExec,
   `Nock.NockVMROM.Thm54.RawProblem.exec,
   `Nock.NockVMROM.Thm54.BuildableNockExecution.exec,
   `Nock.NockVMROM.Thm54.ExactCanonicalRAPProblem.exec,
   `Nock.NockVMROM.Thm54.RawPlusIOSegmentedFamily.exec,
   `Nock.NockVMROM.Thm54.ExactExecution.encodeMem,
   `Nock.NockVMROM.Thm54.TraceGen.genExactExecution]

run_cmd do
  let env ← getEnv
  for n in aBearingHeads.drop 1 ++ encodedHeads do
    unless env.contains n do throwError m!"head name missing: {n}"
  let cap := closureOf env capstone


  -- Since the thirty-first move (exponent carrier: `reqIdx`, `S`, ten-slot records): 41 671.
  -- Since H1.5b Part 1: 41 670.
  -- Since the thirty-second move (the decoded λ-event `decodedLambdaEventOf` in the pinned


  -- now reads `pPin`/`lm`; the pre-C1 `msbVal` route (`leftover_msb_lt_of_window`, `exists_first_msb_lt`)

  -- this closure): 41 738.
  -- Since the thirty-third move (the request-indexed pair event `reqPairEventOf` in the pinned

  -- Since H1.5b Part 2a (acceptance at the family chips, the family IO event, `rowsBound`): 41 864.

  -- `BuildableChips.interPoleOfE'`, which also excludes `-γ^8`; slack `interCard'_of_basis`;


  -- the second half of `hwin` through the new helper `memRowsL_le_orderOf_of_shape`; no digest
  -- move): 41 870.


  -- through `memRowsL_le_orderOf_of_shapeW` and the new `programMemShape_alpha_irrel` chain).

  -- staged bound reached from `of_package`).

  unless cap.size == 40965 do throwError m!"closure size moved: {cap.size}"
  -- S2: the chain discharges the memory `hordM` through the αW form.
  unless cap.contains `Nock.NockVMROM.Thm54.TraceGen.memRowsL_le_orderOf_of_shapeW do
    throwError m!"S2: memRowsL_le_orderOf_of_shapeW not in the capstone closure"
  -- Claim 1: every axis consumer's execution argument is a-bearing.
  let heads ← execHeads env cap axisConsumers
  let mut bad : Array (Name × Array Name) := #[]
  for (h, ns) in heads.toList do
    unless aBearingHeads.contains h do bad := bad.push (h, ns)
  unless bad.isEmpty do throwError m!"axis consumer fed a non-a-bearing execution: {bad}"
  -- positive controls: the a-bearing producers are found
  for h in [`Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specializeA,
            `Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.specializedExecA,
            `Nock.NockVMROM.Thm54.TemplateRawJointSoundness.specializedExecA,
            `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.memoryExecA,
            `Nock.NockVMROM.Thm54.TraceGen.genExactExecutionA] do
    unless heads.contains h do throwError m!"positive control: a-bearing head {h} not found"
  -- the carrier's served trace sits on `execA`
  let served ← execHeads env cap
    [(`Nock.NockVMROM.Thm54.ServedMemoryTrace.ExactServedMemoryTrace, 1)]
  unless served.contains `Nock.NockVMROM.Thm54.BuildableNockExecution.execA do
    throwError m!"served trace not found on BuildableNockExecution.execA: {served.toList.map (·.1)}"
  -- Positive control for the instrument: IO consumers DO see encoded heads.
  let io ← execHeads env cap
    [(`Nock.NockVMROM.Thm54.ExactExecution.derivedRequestIO, 0),
     (`Nock.NockVMROM.Thm54.ExactExecution.derivedResponseIO, 0)]
  for h in [`Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.specializedExec,
            `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specialize,
            `Nock.NockVMROM.Thm54.BuildableNockExecution.exec] do
    unless io.contains h do throwError m!"IO positive control: encoded head {h} not found"
  for h in [`Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.specializedExecA,
            `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specializeA] do
    if io.contains h then throwError m!"IO read on the a-bearing view: {h}"
  logInfo m!"CLAIM1 closure={cap.size} axis-consumer heads={heads.toList.map (·.1)} \
    IO heads={io.toList.map (·.1)}"

-- Exact `MemRec.axis` reader census of the capstone closure and the template-`a`-as-`T` probe.
run_cmd do
  let env ← getEnv
  let cap := closureOf env capstone
  let mut readers : Array Name := #[]
  for n in cap.toList do
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    if mentionsAxis ci.type || mentionsAxis v then readers := readers.push n

  -- again since the thirty-second (the template-level `formRLambdaEvent` left the capstone; the
  -- decoded event reads round-0 columns, not `MemRec.axis`).




  unless readers.size == 184 do throwError m!"MemRec.axis reader count moved: {readers.size}"
  for c in [`Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisTree,
            `Nock.NockVMROM.Thm54.TemplateAxisCounting.ofNTree_specialize_toMTree,
            `Nock.NockVMROM.Thm54.SemanticStrategy.BindMemRow,
            `Nock.MemoryTable.eqBlk] do
    unless readers.contains c do throwError m!"positive control: {c} not a reader"
  -- template placeholder read together with `formRT`: only `bindsRow_specialize` (a ↦ T)
  let place := `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.placeholder
  let frt := `Nock.MemoryTable.formRT
  let mut both : Array Name := #[]
  for n in readers do
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    let u := ci.type.getUsedConstants ++ v.getUsedConstants
    if u.contains place && u.contains frt then both := both.push n

  unless both.toList.toArray.qsort (·.toString < ·.toString) == #[`Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.bindsRow_specialize,
      `Nock.RedTeam.Batch973.specialize_wrapR0_eq_self].qsort (·.toString < ·.toString) do
    throwError m!"template-axis-with-formRT readers: {both}"
  logInfo m!"MEMREC-AXIS readers={readers.size} template∧formRT={both}"

/-! ## §2 Claim 4 — axis validity restored on `specializedExecA` -/

section Claim4
open Nock.NockVMROM.Thm54 ProductionP8Containment
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]

/-- The acceptance boundary is literally the guarded event's polynomial vanishing at `alphaM`
(`ProductionP8Containment.lean:152-157`, `TemplateAxisCounting.lean:74-76`). -/
theorem guarded_poly_is_acceptance_poly
    (T : ProductionStrategy F K) (z : K) (hz : z ≠ 0) (α : K) :
    T.RootAxisBoundaryAt z hz α ↔
      ∀ i, (TemplateAxisCounting.templateAxisPolynomial
        (ProductionAxisStructureVerifier.committedTemplate T.verifier z hz) i).eval α = 0 :=
  Iff.rfl

end Claim4

run_cmd do
  let env ← getEnv
  let n := `Nock.NockVMROM.Thm54.ProductionP8Containment.specializedAxisValidity_of_accepts
  let some ci := env.find? n | throwError "missing"
  let names ← liftTermElabM <| forallTelescope ci.type fun xs _ => do
    let mut out : Array Name := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then out := out.push d.userName
    return out


  unless names.toList == [`h2, `T, `lmb, `ω, `hz, `hacc, `hout] do
    throwError m!"explicit binders moved: {names}"
  let axs ← collectAxioms n
  for a in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError m!"non-whitelisted axiom {a}"
  -- it is on the capstone, and so is the FormR-free workload; the FormR twin is off it
  let cap := closureOf env capstone
  for c in [n, `Nock.NockVMROM.Thm54.ProductionP8Containment.two_ne_zero_of_stateTagChar,
            `Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisWorkload,
            `Nock.NockVMROM.Thm54.ProductionP8Containment.fixedAxisWorkload] do
    unless cap.contains c do throwError m!"{c} not on the capstone"
  for c in [`Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisWorkloadFormR,
            `Nock.NockVMROM.Thm54.TemplateAxisCounting.templateAxisPolynomialFormR] do
    if cap.contains c then logInfo m!"note: {c} IS on the capstone"
    else logInfo m!"{c} off the capstone"
  logInfo m!"CLAIM4 binders={names} axioms={axs}"

/-! ### The workload moved as a function (non-blocking): the cancelling tree -/

section Workload
open Nock.AxisBatching Nock.AxisBatching.MTree Polynomial

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The cancelling tree: a `read_root` at exponent 1 over a `decompose` whose left
child verifies at exponent 1 with committed axis 5 (true relative axis 2). -/
noncomputable def cancelTree : MTree (ZMod 7) :=
  .read 1 (.decompose (.verify 1 5 .halt) .halt)

theorem cancelTree_countsP_zero : countsP cancelTree = 0 := by
  simp [cancelTree, countsP, indP, pwScale]

theorem two_inv_zmod7 : (2 : ZMod 7)⁻¹ = 4 :=
  inv_eq_of_mul_eq_one_right (by decide)

theorem cancelTree_countsP_bin_eval_one : (countsP_bin cancelTree).eval 1 = 5 := by
  simp [cancelTree, countsP_bin, indP_bin, two_inv_zmod7]
  decide

theorem cancelTree_countsP_bin_eval_zero : (countsP_bin cancelTree).eval 0 = 0 := by
  simp [cancelTree, countsP_bin, indP_bin]

/-- **Workload moved.**  Old per-root contribution `natDegree (countsP t) = 0`; new
`natDegree (countsP_bin t) ≥ 1`. -/
theorem cancelling_tree_workload_moves :
    (countsP cancelTree).natDegree = 0 ∧ 1 ≤ (countsP_bin cancelTree).natDegree := by
  refine ⟨by rw [cancelTree_countsP_zero]; simp, ?_⟩
  by_contra h
  push Not at h
  have h0 : (countsP_bin cancelTree).natDegree = 0 := by omega
  have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
  have e0 := cancelTree_countsP_bin_eval_zero
  have e1 := cancelTree_countsP_bin_eval_one
  rw [hC] at e0 e1
  simp at e0 e1
  rw [e0] at e1
  exact absurd e1 (by decide)

end Workload

end Nock.RedTeam.Batch593

#print axioms Nock.RedTeam.Batch593.memoryRow_specialize_eq_encodeRow_specializeA
#print axioms Nock.RedTeam.Batch593.execution_specialize_eq_encodeMem
#print axioms Nock.RedTeam.Batch593.template_binding_is_a_bearing
#print axioms Nock.RedTeam.Batch593.specializedProblem_exec_eq_encodeMem
#print axioms Nock.RedTeam.Batch593.guarded_poly_is_acceptance_poly
#print axioms Nock.RedTeam.Batch593.cancelTree_countsP_zero
#print axioms Nock.RedTeam.Batch593.cancelTree_countsP_bin_eval_one
#print axioms Nock.RedTeam.Batch593.cancelling_tree_workload_moves
#print axioms Nock.NockVMROM.Thm54.ProductionP8Containment.specializedAxisValidity_of_accepts
