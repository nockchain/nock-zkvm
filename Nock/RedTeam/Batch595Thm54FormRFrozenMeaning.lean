/-
  Nock/RedTeam/Batch595Thm54FormRFrozenMeaning.lean

  Identity.

  Instruments (elaboration-time; a false assertion FAILS THE BUILD):
  * `closureOf` — full transitive closure, types + values, theorem proofs included
    (`value? (allowOpaque := true)`).  This is the "what the capstone uses" walk.
  * `meaningClosure` — types; definition values; constructor types; theorem PROOFS EXCLUDED.

  Claim 5 (`CprimeCoherent`, `hzc`), §1–§3:
  * §1  `ExactExecution.CprimeCoherent` is NOT in the `nockCompiles_zmod` closure (41 475 constants,
    proofs included), nor in the closure of `optimizedFullStrictNockVMROM_of_package`, nor in the
    statement's meaning closure.  Positive controls: the walk finds the of-package theorem,
    `acceptance_outside_failure_implies_target`, `OptimizedComputeHostileAccumulator.rowRecord`,
    `memoryExecA`; and finds `CprimeCoherent` from `sampled_inter_event_good_of_acceptance`.
  * §2  Every user of the `hzc` premise (`canonical_inter_not_hostile_failure`,
    `canonical_allRow_not_hit`) in the environment is a closed concrete-fixture theorem off the
    capstone; each discharges `hzc` (`inactive_cprime_one_legacy` / `_oneS` / `_oneD`).
  * §3  What `CprimeCoherent` says: exactly "`C'` is a function of the stored row record"
    (`cprimeCoherent_iff_exists_fun`).  It is not vacuous: Form R's row record keeps only the
    bit-length of `a` (`T = λ^{size a − 1}`), so axes `2` and `3` at one timestamp give the SAME row
    record and DIFFERENT `C'` (`formRRow_two_three_eq`, `formRCprime_two_three_ne`, `ZMod 73`,
    `λ = formRDefault = 2`).  Two such rows violate `CprimeCoherent`; only unique timestamps exclude
    them.
  * §4  `rowRecord` slot 6 / slot 8 are the Form R slot gates, no placeholder (`rfl`).
  * §5  The 18 frontier additions are all inside the statement's meaning closure (none is dead
    weight).  17 are watchlist entries; one (`memoryExecA`) is reached at ring one.
  * The watchlisted `MemoryRowTemplate.specialize` is `encodeRow (T.specializeA α)` —
    its fingerprint hashes those NAMES only.  `formRDefault` is load-bearing: at `λ = 1` the row
    record forgets the axis entirely (`formRRow_lambda_one_forgets`).
    `formRRow_lambda_one_forgets` still holds as a statement about `formRRow`.]
-/
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.OptimizedStrictFullPackageConcrete
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusCompleteFalseAcceptance
import Nock.NockVMROM.Thm54.DistinctCensusFold2
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch595

open Lean Meta Elab Command

/-! ## §0 Instruments -/

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

/-- Meaning closure: types, definition values, constructor types; theorem proofs excluded. -/
partial def meaningClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut es := #[ci.type]
    match ci with
    | .defnInfo d => es := es.push d.value
    | .inductInfo iv =>
        for c in iv.ctors do
          if let some cc := env.find? c then es := es.push cc.type
    | _ => pure ()
    for e in es do
      for c in e.getUsedConstants do
        if !seen.contains c then stack := stack.push c
  return seen

def capstone : Name := `Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
def ofPackage : Name :=
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
def statement : Name :=
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement
def pkg : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage
def cprimeCoherent : Name := `Nock.NockVMROM.Thm54.ExactExecution.CprimeCoherent
def interEvent : Name := pkg ++ `sampled_inter_event_good_of_historical
def genDischarge : Name := `Nock.NockVMROM.Thm54.TraceGen.genExactExecution_cprimeCoherent
def hzcUsers : List Name :=
  [`Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists.canonical_inter_not_hostile_failure,
   `Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists.canonical_allRow_not_hit]

def assertExists (env : Environment) (n : Name) : CommandElabM Unit := do
  unless (env.find? n).isSome do throwError m!"missing constant {n}"

/-! ## §1 `CprimeCoherent` is not on the capstone -/

run_cmd do
  let env ← getEnv
  for n in [capstone, ofPackage, statement, cprimeCoherent, interEvent, genDischarge] do
    assertExists env n
  let cap := closureOf env capstone
  for n in [ofPackage, statement, pkg ++ `acceptance_outside_failure_implies_target309,
      `Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.rowRecord,
      `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.memoryExecA,
      `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.encodeRow] do
    unless cap.contains n do throwError m!"positive control failed: {n} not in capstone closure"
  -- the instrument does see `CprimeCoherent` where it is used
  unless (closureOf env interEvent).contains cprimeCoherent do
    throwError "positive control failed: CprimeCoherent not found from its consumer"
  unless (closureOf env genDischarge).contains cprimeCoherent do
    throwError "positive control failed: CprimeCoherent not found from its discharge"
  -- the measurement
  for n in [cprimeCoherent, interEvent, genDischarge,
      `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.memoryCompletenessHyps,
      `Nock.NockVMROM.Thm54.SampledIOSameExecution.inter_coins_not_failure] ++ hzcUsers do
    if cap.contains n then throwError m!"{n} IS in the nockCompiles_zmod closure"
  let ofp := closureOf env ofPackage
  if ofp.contains cprimeCoherent then throwError "CprimeCoherent in of_package closure"
  if (meaningClosure env statement).contains cprimeCoherent then
    throwError "CprimeCoherent in the statement's meaning"
  logInfo m!"B595-S1 capstone closure {cap.size}; of_package closure {ofp.size}; CprimeCoherent, sampled_inter_event_good_of_acceptance, genExactExecution_cprimeCoherent, memoryCompletenessHyps, inter_coins_not_failure, hzc users: all OUT"

/-! ## §2 Every `hzc` consumer is a discharged, off-capstone fixture theorem -/

run_cmd do
  let env ← getEnv
  let cap := closureOf env capstone
  let mut users : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`Nock.RedTeam).isPrefixOf n then continue
    if hzcUsers.contains n then continue
    if n.isInternal then continue
    let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
    if hzcUsers.any (fun u => v.getUsedConstants.contains u) then
      users := users.push n
  unless users.size == 0 do throwError m!"expected 0 hzc users after 2a, got {users}"
  for u in users do
    if cap.contains u then throwError m!"hzc user {u} IS on the capstone"
    let some ci := env.find? u | throwError "?"
    unless ci matches .thmInfo _ do throwError m!"hzc user {u} is not a theorem"
    let ax ← liftCoreM (Lean.collectAxioms u)
    if ax.contains ``sorryAx then throwError m!"{u} uses sorryAx"
  logInfo m!"B595-S2 hzc users (all theorems, all off the capstone, no sorryAx): {users}"

-- the discharges themselves
#check @Nock.NockVMROM.Thm54.ConcreteStrictPackage.inactive_cprime_one_legacy
#check @Nock.NockVMROM.Thm54.MultiRootServedFixture.inactive_cprime_oneS
#check @Nock.NockVMROM.Thm54.DistinctCensusExecution.inactive_cprime_oneD

/-! ## §3 What `CprimeCoherent` says, and that it is a real restriction -/

section Content

open Nock.NockVMROM.Thm54

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `CprimeCoherent` is exactly: `C'` is a function of the stored row record. -/
theorem cprimeCoherent_iff_exists_fun {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.CprimeCoherent ↔
      ∃ cp : ComputeTable.MemRec K → K,
        ∀ row ∈ exec.memoryRows, row.2.2.cprime = cp row.2.2.mem :=
  ⟨fun h => ⟨exec.cprimeOf, ExactExecution.cprime_eq_cprimeOf h⟩,
   fun ⟨cp, h⟩ => ExactExecution.cprimeCoherent_of_fun cp h⟩

end Content

section Witness

instance : Fact (Nat.Prime 73) := ⟨by norm_num⟩

abbrev Z := ZMod 73

/-- Two a-bearing records at one timestamp, axes `2` and `3`. -/
def r2 : ComputeTable.MemRec Z := { ComputeTable.MemRec.zero with axis := 2, ts := 5 }
def r3 : ComputeTable.MemRec Z := { ComputeTable.MemRec.zero with axis := 3, ts := 5 }

theorem ringChar_Z : ringChar Z = 73 := ZMod.ringChar_zmod_n 73

theorem nockAxisOf_two : MemoryTable.nockAxisOf (2 : Z) = 2 := by
  have := MemoryTable.nockAxisOf_natCast (K := Z) (a := 2) (by rw [ringChar_Z]; norm_num)
  simpa using this

theorem nockAxisOf_three : MemoryTable.nockAxisOf (3 : Z) = 3 := by
  have := MemoryTable.nockAxisOf_natCast (K := Z) (a := 3) (by rw [ringChar_Z]; norm_num)
  simpa using this

/-- The executed (row-level) records agree: `T = λ^{size a − 1} = λ` for both. -/
theorem formRRow_two_three_eq :
    NockVM.formRRow r2 MemoryTable.formRDefault = NockVM.formRRow r3 MemoryTable.formRDefault := by
  simp only [NockVM.formRRow, r2, r3, nockAxisOf_two, nockAxisOf_three, MemoryTable.formRT]
  rw [show MemoryTable.formRCertShift 2 = MemoryTable.formRCertShift 3 from by decide]

/-- …but their `C'` differ (`n − 1 = size 73 − 1 = 6`; certificate bits of `2` vs `3`). -/
theorem formRCprime_two_three_ne :
    NockVM.formRCprime r2 MemoryTable.formRDefault ≠
      NockVM.formRCprime r3 MemoryTable.formRDefault := by
  simp only [NockVM.formRCprime, r2, r3, nockAxisOf_two, nockAxisOf_three, MemoryTable.formRC,
    MemoryTable.pwScaleExp, ringChar_Z, MemoryTable.formRDefault]
  decide

/-- `formRDefault` is load-bearing: at `λ = 1` every row record forgets its axis. -/
theorem formRRow_lambda_one_forgets (r r' : ComputeTable.MemRec Z)
    (h : r.root = r'.root ∧ r.child = r'.child ∧ r.ts = r'.ts) :
    NockVM.formRRow r 1 = NockVM.formRRow r' 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [NockVM.formRRow, MemoryTable.formRT_one]
  cases r; cases r'; simp_all

end Witness

/-! ## §4 The consumed failure event's records -/

section Records

open Nock.NockVMROM.Thm54 OptimizedComputeCorrectedFinal OptimizedComputeSubstitution

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem rowRecord_slot6 (env : CorrectedFinalTypedEnv F K) (j : Fin 3) :
    OptimizedComputeHostileAccumulator.rowRecord env j 6 =
      ((sampledSlotT .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace).eval
        env.toSourceEnv := rfl

theorem rowRecord_slot8 (env : CorrectedFinalTypedEnv F K) (j : Fin 3) :
    OptimizedComputeHostileAccumulator.rowRecord env j 8 =
      ((sampledSlotC .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace).eval
        env.toSourceEnv := rfl

theorem rowRecord_slot7 (env : CorrectedFinalTypedEnv F K) (j : Fin 3) :
    OptimizedComputeHostileAccumulator.rowRecord env j 7 =
      ((computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + 7)).subst finalSampledNamespace).eval
        env.toSourceEnv := rfl

open OptimizedStrictFullPackage in
/-- The IO work the capstone prices is unchanged: arity `9`, `3·compRows` requests, `memRows`
responses. -/
theorem hostileIOWork_eq [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.hostileIOWork =
      FiniteIO.ioFailureUnionBound 10 (3 * P.optimized.family.problem.cfg.compRows)
        P.optimized.family.problem.cfg.memRows (Fintype.card K) := rfl

end Records

-- Positive control: the
-- consumed failure event does mention the tuple type.
run_cmd do
  let env ← getEnv
  let tup := `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedProductionChallengeTuple
  assertExists env tup
  for n in [pkg ++ `hostileRecords, pkg ++ `hostileRequests, pkg ++ `hostileResponses,
      `Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator.rowRecord] do
    let some ci := env.find? n | throwError m!"missing {n}"
    if ci.type.getUsedConstants.contains tup then throwError m!"{n} depends on the tuple"
  let some fe := env.find? (pkg ++ `optimizedFailureEvent) | throwError "missing event"
  unless fe.type.getUsedConstants.contains tup do
    throwError "positive control failed: optimizedFailureEvent does not mention the tuple"
  logInfo "B595-S4 hostile records are tuple-free; optimizedFailureEvent is over the tuple"

/-! ## §5 The 18 frontier additions all belong; §6 the unpinned encode core -/

def frontierAdds : List Name :=
  [`Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.correctedFinalTypedCompile,
   `Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.correctedLowerFinal,
   `Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.formRLamFactor,
   `Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.formRLamHPin,
   `Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.formRLamPins,
   `Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.formRLamTPin,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.lamPowVar,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledCprime,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledDenom,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledGSel,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledLam,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledRecordRLC,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledSlotC,
   `Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledSlotT,
   `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.memoryExecA,
   `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specialize,
   `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specialize,
   `Nock.NockVMROM.Thm54.Thm54Resources.rangeGates]

def unpinnedEncodeCore : List Name :=
  [`Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.encodeRow,
   `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specializeA,
   `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.ExactExecutionTemplate.specializeA,
   `Nock.NockVMROM.Thm54.ExactExecution.encodeMem,
   `Nock.NockVM.formRRow, `Nock.NockVM.formRCprime, `Nock.MemoryTable.formRDefault,
   `Nock.MemoryTable.formRT, `Nock.MemoryTable.formRC, `Nock.MemoryTable.nockAxisOf]

/-- **Drift since the λ fix.**  Since the
λ fix the row's `λ` is the sampled config coin, and `MemoryTable.formRDefault` is measured NOT in
the statement's meaning closure (fixture-only; the other nine encode-core names stay IN). -/
def post28thMeaningDropped : List Name := [`Nock.MemoryTable.formRDefault]

run_cmd do
  let env ← getEnv
  let st := meaningClosure env statement
  for n in post28thMeaningDropped do
    unless unpinnedEncodeCore.contains n do throwError m!"drift list: {n} not in unpinnedEncodeCore"
  for n in frontierAdds ++ unpinnedEncodeCore do
    assertExists env n
    if post28thMeaningDropped.contains n then
      if st.contains n then
        throwError m!"{n} is back in the statement's meaning closure (post-λ-fix drift)"
    else
      unless st.contains n do throwError m!"{n} not in the statement's meaning closure"
  -- the watchlisted `specialize` names the encode core only by reference
  let sp := `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.specialize
  let some ci := env.find? sp | throwError "?"
  let v := (ci.value? (allowOpaque := true)).getD (.sort .zero)
  unless v.getUsedConstants.contains
      `Nock.NockVMROM.Thm54.SemanticTimestampStrategy.MemoryRowTemplate.encodeRow do
    throwError "specialize does not reference encodeRow"
  logInfo m!"B595-S5 statement meaning closure {st.size}: all 18 frontier adds IN; encode core: 9 IN, formRDefault OUT (since the λ fix)"

end Nock.RedTeam.Batch595

#print axioms Nock.RedTeam.Batch595.cprimeCoherent_iff_exists_fun
#print axioms Nock.RedTeam.Batch595.formRRow_two_three_eq
#print axioms Nock.RedTeam.Batch595.formRCprime_two_three_ne
#print axioms Nock.RedTeam.Batch595.formRRow_lambda_one_forgets
#print axioms Nock.RedTeam.Batch595.rowRecord_slot6
#print axioms Nock.RedTeam.Batch595.rowRecord_slot8
#print axioms Nock.RedTeam.Batch595.rowRecord_slot7
#print axioms Nock.RedTeam.Batch595.hostileIOWork_eq
