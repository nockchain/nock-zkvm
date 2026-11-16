/-
  Nock/RedTeam/Batch596Thm54FormRResiduals.lean

  ENVIRONMENT.

  Instruments (elaboration time; a false assertion fails the check): `closureOf` (type + value,
  theorem bodies included, `value?

  What is compiled here:
  * §1 Claim 6, binder walk: `nockCompiles_zmod` is 26 total / 13 explicit, explicit names end
    `hwidth`, `hax`; `hfirst` / `hmore` / `hbasis` are gone.  CONFIRMED.
  * §2 Claim 6, discharges in the closure (positive controls): `romTree_assigned_request_axes_lt`,
    `genBuildableOfProgram_laterSeedZeros`, `compilerBasis_formR` reached from `nockCompiles_zmod`.
    Axioms of the capstone and the three dischargers ⊆ {propext, Classical.choice, Quot.sound}.
  * OV says hypotheses "unchanged" and lists the residuals
    without recording either strengthening.  `formRWidth_third_redundant`: the new conjunct of
    `hwidth` is implied by the explicit `hp : 25 ≤ p` and was left as a residual.
  * §4 Claim 7: `formR_at_two` is contentless (`formR_at_two_any_lambda`: the same statement holds
    at every `λ`, by commutativity) and is not reached from the capstone.  `hp64` names nothing in
    the closure.  Stub finding: no `…_stub` constant exists; `genExactExecution_laterSeedZeros`
    is a theorem in the closure.
  * §6 Claim 8: no compute-IO transport / alias / wrap-join / `MemoryTreeBindsA` constant is in the
    capstone closure.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch596

open Lean Meta Elab Command

/-! ## §0 Instruments -/

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

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

def capstone : Name := `Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod

def contains (s : String) (p : String) : Bool := (s.splitOn p).length > 1

/-! ## §1 Claim 6: binder walk -/

run_cmd liftTermElabM do
  let tel ← binderTelescope capstone
  let expl := tel.filterMap fun (nm, bi) => if bi == .default then some nm else none
  unless tel.size == 27 do throwError m!"total binders {tel.size}, expected 27"
  unless expl.size == 14 do throwError m!"explicit binders {expl.size}, expected 14"
  let names := expl.toList.map toString
  -- Since the λ fix: `lmb` after `α`,
  -- `hp64` after `hp`, and `hwidth` / `hax` are gone (lemmas `FormRWidth_of_hp64` /
  -- `genComputeRows_rowsFormRAxisBound`).  Totals 26 / 13 are unchanged.
  unless names == ["α", "αW", "lmb", "hrun", "hbound", "hs", "hf", "hΛp", "hp", "hp64", "hK", "hF",
      "hwin", "hKszChar"] do
    throwError m!"explicit names {names}"
  for gone in ["hfirst", "hmore", "hbasis", "hwidth", "hax"] do
    if tel.any (fun (nm, _) => nm.toString == gone) then throwError m!"{gone} still a binder"
  unless tel.any (fun (nm, _) => nm.toString == "hp64") do throwError "hp64 not a binder"
  logInfo m!"B596 binder walk nockCompiles_zmod = {tel.size}/{expl.size} {names}"

/-! ## §2 Claim 6: dischargers reached; axioms whitelisted -/

def dischargers : List Name :=
  [``Nock.NockVMROM.Thm54.TraceGen.romTree_assigned_request_axes_lt,
   ``Nock.NockVMROM.Thm54.TraceGen.genBuildableOfProgram_laterSeedZeros,
   ``Nock.NockVMROM.Thm54.TraceGen.genExactExecution_laterSeedZeros,
   ``Nock.NockVMROM.Thm54.TraceGen.compilerBasis_formR,
   ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p68]

def whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstone
  for n in dischargers do
    unless cap.contains n do throwError m!"positive control failed: {n} not in closure"
  for n in capstone :: dischargers do
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless whitelist.contains a do throwError m!"{n} uses non-whitelisted axiom {a}"
  logInfo m!"B596 closure size {cap.size}; dischargers reached; axioms whitelisted"

/-! ## §3 Residual binders strengthened (non-blocking disclosure finding) -/

open Nock.NockVMROM.Thm54 in
theorem formRWidth_three_conjuncts (F : Type) [Field F] :
    OptimizedComputeFinalTrace.FormRWidth F ↔
      (OptimizedComputeRangeCertificate.formRN F ≤ 64 ∧
        0 < OptimizedComputeRangeCertificate.formRN F ∧ 3 < ringChar F) := Iff.rfl

/-- The new third conjunct is implied by the capstone's explicit `hp : 25 ≤ p`; leaving it in the
residual `hwidth` is redundant, not a gap. -/
theorem formRWidth_third_redundant (p : ℕ) [Fact p.Prime] (hp : 25 ≤ p) :
    3 < ringChar (ZMod p) := by
  rw [ZMod.ringChar_zmod_n]; omega

open Nock.NockVMROM.Thm54 OptimizedComputeFinalTrace in
/-- `FormRAxisBound` now also demands the `𝕂` record axis equal the base residue. -/
theorem formRAxisBound_has_K_conjunct
    {p : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
    [DecidableEq K] [CharP K p]
    {R : PlusIOSegmentedFamily F K} (A : SampledIOSameExecutionAssignment R p)
    (b : Module.Basis (Fin 3) F K) (h : FormRAxisBound A b)
    (i : Fin R.problem.cfg.compRows) (L : F) (hL : axisLeafCoord A b i = some L) :
    ∃ a : ℕ, ((a : ℕ) : K) = axisLeafK A i := by
  obtain ⟨a, -, -, -, -, haK⟩ := h i L hL
  exact ⟨a, haK⟩

/-! ## §4 Claim 7: `formR_at_two` contentless; `hp64` absent; stubs gone -/

/-- `formR_at_two` holds with `2` replaced by ANY `λ`: it is commutativity, with no Form R
content.  It must not be cited as a paper equivalence. -/
theorem formR_at_two_any_lambda {K : Type} [Field K] (lmb : K) (ax : ℕ) (ts : K) :
    lmb ^ MemoryTable.pwScaleExp K * ts = ts * lmb ^ MemoryTable.pwScaleExp K ∧
      lmb ^ MemoryTable.pwScaleExp K * MemoryTable.formRT lmb ax * ts =
        MemoryTable.formRT lmb ax * ts * lmb ^ MemoryTable.pwScaleExp K :=
  ⟨by ring, by ring⟩

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstone
  -- formR_at_two exists (positive control for the name search) and is off the capstone
  unless env.contains ``Nock.MemoryTable.formR_at_two do throwError "formR_at_two missing"
  if cap.contains ``Nock.MemoryTable.formR_at_two then throwError "formR_at_two in closure"
  -- no constant in the closure is named after stubs
  for p in ["_stub", "Stub"] do
    let hits := cap.toList.filter (fun n => contains n.toString p)
    unless hits.isEmpty do throwError m!"{p} in closure: {hits}"
  -- Since the
  -- λ fix: exactly `FormRWidth_of_hp64` (and its auxiliary `_proof_` constants),
  -- the lemma that discharges the former `hwidth` from the binder `hp64`.
  let hp64Hits := cap.toList.filter (fun n => contains n.toString "hp64")
  let hp64Parents := hp64Hits.filter (fun n => !contains n.toString "._proof")
  unless hp64Parents == [``Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.FormRWidth_of_hp64] do
    throwError m!"hp64 in closure: {hp64Hits}"
  -- no stub constant anywhere in Nock.NockVMROM
  let stubs := env.constants.toList.filter fun (n, _) =>
    contains n.toString "Nock.NockVMROM" && contains n.toString "_stub"
  unless stubs.isEmpty do throwError m!"stub constants exist: {stubs.map (·.1)}"
  logInfo "B596 formR_at_two off-capstone; hp64-named closure constant = FormRWidth_of_hp64 only; no stub constant"


run_cmd do
  let env ← getEnv
  let lastIs (s : String) (n : Name) : Bool := match n with
    | .str _ l => l == s
    | _ => false
  -- positive control: the search finds a name that does exist
  let ctl := env.constants.toList.filter fun (n, _) => lastIs "formR_at_two" n
  unless ctl.length == 1 do throwError m!"control: formR_at_two hits {ctl.length}"
  for s in ["rootzero_general", "formR_product_general", "forest_bfs_eq_cert",
      "formR_TC_transport"] do
    let hits := env.constants.toList.filter fun (n, _) => lastIs s n
    unless hits.isEmpty do throwError m!"{s} exists: {hits.map (·.1)}"
  logInfo "B596 OV-cited names absent at f74a7d4f: rootzero_general, formR_product_general, forest_bfs_eq_cert, formR_TC_transport"

/-! ## §6 Claim 8: no compute-only canonicity / H1 machinery on the capstone -/

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstone
  for p in ["ComputeIOTransport", "alias_", "wrapJoin", "wrapSpecializeJoin",
      "MemoryTreeBindsA", "WrapMemoryIdentity", "CprimeCoherent", "goldilocks_prime"] do
    let hits := cap.toList.filter (fun n => contains n.toString p &&
      !(match env.getModuleIdxFor? n with
        | some i => (`Nock.NockVMROM.Thm54.P8Core).isPrefixOf (env.header.moduleNames[i.toNat]!)
        | none => false))
    unless hits.isEmpty do throwError m!"{p} in closure: {hits.take 5}"
  logInfo "B596 no H1 transport / wrap / provisional-binds / CprimeCoherent constant in closure"

end Nock.RedTeam.Batch596

#print axioms Nock.RedTeam.Batch596.formRWidth_three_conjuncts
#print axioms Nock.RedTeam.Batch596.formRWidth_third_redundant
#print axioms Nock.RedTeam.Batch596.formRAxisBound_has_K_conjunct
#print axioms Nock.RedTeam.Batch596.formR_at_two_any_lambda
