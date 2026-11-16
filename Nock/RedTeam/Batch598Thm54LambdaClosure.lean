/-
  Nock/RedTeam/Batch598Thm54LambdaClosure.lean

  Instrument: `closureOf` walks type AND value (`value? Every absence claim has a positive
  control from the same instrument. Identity; read-only against the target build.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch598

open Lean Meta Elab Command

/-- Full transitive closure: types and values, theorem proofs included. -/
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

def zmod : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def capstone : Name := ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
def formRDefault : Name := ``Nock.MemoryTable.formRDefault

-- Check 6/7/4: `formRDefault`, `compilerLam`, `Classical.skolem` in the proof closure of
-- `nockCompiles_zmod`; `compilerLam` must not even exist; positive controls on the same walk.
run_cmd do
  let env ← getEnv
  let cl := closureOf env zmod
  logInfo m!"closure(nockCompiles_zmod) = {cl.size} constants"
  -- positive controls: things that MUST be in the closure
  for pc in [ ``Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.FormRWidth_of_hp64
            , ``Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound
            , ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
            , ``Nock.NockVMROM.Thm54.ChallengeVector.lam
            , ``Nock.MemoryTable.Pub.lambda ] do
    unless cl.contains pc do throwError m!"positive control missing from closure: {pc}"
  -- `compilerLam` does not exist in the environment at all
  for cand in [`Nock.NockVMROM.Thm54.TraceGen.GoodSeed.compilerLam, `Nock.NockVMROM.Thm54.TraceGen.compilerLam] do
    if env.contains cand then throwError m!"compilerLam exists: {cand}"
  -- λ-literal: `formRDefault` reachable from the ∀-program theorem?
  if cl.contains formRDefault then
    logWarning m!"formRDefault IS in the proof closure of nockCompiles_zmod (see check below for the route)"
  else
    logInfo m!"formRDefault NOT in closure(nockCompiles_zmod)"
  -- Report only.
  logInfo m!"Classical.skolem in full closure(nockCompiles_zmod): {cl.contains ``Classical.skolem}"
  -- Record their presence for the report.
  logInfo m!"FormRWidth in proof closure: {cl.contains ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.FormRWidth}; FormRAxisBound in proof closure: {cl.contains ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.FormRAxisBound}"

-- Which constants in the closure mention `formRDefault` directly (the route, if any).
run_cmd do
  let env ← getEnv
  let cl := closureOf env zmod
  let mut hits : Array Name := #[]
  for n in cl.toList do
    let some ci := env.find? n | continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    if (ci.type.getUsedConstants ++ v.getUsedConstants).contains formRDefault then
      hits := hits.push n
  logInfo m!"direct users of formRDefault inside closure(nockCompiles_zmod): {hits}"

-- Capstone closure: same questions from `optimizedFullStrictNockVMROM_of_package`.
run_cmd do
  let env ← getEnv
  let cl := closureOf env capstone
  logInfo m!"closure(of_package) = {cl.size}; formRDefault ∈ ? {cl.contains formRDefault}; skolem ∈ ? {cl.contains ``Classical.skolem}"
  unless cl.contains ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement do
    throwError "positive control: Statement missing from of_package closure"

-- Check 8: `axisLeafK` / `rowAxisLeafK` definitions do not reach the λ-bearing row fields.
run_cmd do
  let env ← getEnv
  for root in [ ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.axisLeafK
              , ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.axisLeafCoord ] do
    let cl := closureOf env root
    let bads := [ ``Nock.MemoryTable.Pub.lambda, ``Nock.MemoryTable.Pub.cprime
               , ``Nock.NockVMROM.Thm54.ChallengeVector.lam, formRDefault
               , ``Nock.NockVM.formRRow, ``Nock.NockVM.formRCprime ]
    let reached := bads.filter cl.contains
    -- coarse walk: a reached projection NAME is not a data dependence; report the direct users
    let mut users : Array Name := #[]
    for n in cl.toList do
      let some ci := env.find? n | continue
      let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
      if (ci.type.getUsedConstants ++ v.getUsedConstants).any (fun c => reached.contains c) then
        users := users.push n
    logInfo m!"{root}: closure {cl.size}; λ-bearing constants reached: {reached}; direct users: {users}"
  -- positive control for this walk: axisLeafCoord reaches encodedRowAt / coreExtensionValue
  let cl := closureOf env ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.axisLeafCoord
  unless cl.contains ``Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace.coreExtensionValue do
    throwError "positive control: axisLeafCoord does not reach coreExtensionValue"

/-! ## Check 5: honest rows at the sampled λ — statements re-elaborated, not just named. -/

section
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

open Nock.NockVMROM.Thm54 in
example (T : SemanticTimestampStrategy.MemoryRowTemplate (K := K)) (α lmb : K) :
    (T.specialize α lmb).2.2.lambda = lmb :=
  SemanticTimestampStrategy.MemoryRowTemplate.specialize_lambda T α lmb

open Nock.NockVMROM.Thm54 in
example {T : SemanticTimestampStrategy.ExactConfigTemplate F K}
    (E : SemanticTimestampStrategy.ExactExecutionTemplate T) (α lmb : K) :
    ∀ row ∈ (E.specialize α lmb).memoryRows, row.2.2.lambda = (T.specialize α lmb).challenges.lam :=
  SemanticTimestampStrategy.ExactExecutionTemplate.specialize_memory_lambda E α lmb

end

-- `OptimizedSameProblemAt.lam_eq` pins the tuple's λ to the objects' λ: the statement, elaborated.
#check @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedSameProblemAt.lam_eq
#check @Nock.NockVMROM.Thm54.TemplateRawJointSoundness.Strategy.familyAt_memoryLambda
#check @Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.honestProductionTuple_lambda

/-! ## Check 7: the λ-irrelevance receipts quantify `lmb₁ lmb₂` on the OUTSIDE (no swap). -/
#check @Nock.NockVMROM.Thm54.TraceGen.GoodSeed.badSeeds_lambda_irrelevant
#check @Nock.NockVMROM.Thm54.TraceGen.GoodSeed.sizeWindowFailureSeeds_lambda_irrelevant
#check @Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_good_seed_of_rom_lambdaFree
#check @Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_vcomp_seed_of_rom_allLambda
#check @Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.formRAxisBound_specialize_lambda_irrel

-- Check 11: axioms
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.genComputeRows_rowsFormRAxisBound
#print axioms Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda.FormRWidth_of_hp64

end Nock.RedTeam.Batch598
