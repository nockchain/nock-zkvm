import Lean
import Nock.NockVMROM.Thm54.HostileSemanticSoundness
import Nock.NockVMROM.Thm54.GeneratedField
import Nock.RedTeam.Batch700Thm54PreSeedCensus
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesHostile
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1400Thm54HostileSemanticSoundness.lean

  * §1 **Constant walk** (`run_cmd`, asserting): what `DeployedAcceptanceAt` READS.  Walk = types and
    definition bodies (theorem proofs not entered; inductive constructors entered only at the root),
    `Nock.*` names, both projection-function constants and primitive `Expr.proj` nodes.  Asserted
    ABSENT at `DeployedAcceptanceAt`: every projection named `strategy`, `objects`, `census`,
    `records` (`P.strategy`, `P.objects`, `P.optimized.objects`, `P.optimized.census`,
    `…sampled.records`) and `OptimizedStrictNockVMROMPackage.sampled`.  Positive control: the same
    walker FINDS `strategy` and `sampled` at the pre-2a predicate `OptimizedHistoricalAcceptanceAt`.
    The package projections the predicate does read are printed (chip inputs and the public claim).
  * §2 **Import walk**: `P8Core.HostileSemanticSoundnessEv`'s closure excludes the statement module and
    has only the allowed 10 RedTeam modules; positive control `Thm54.HostileSemanticSoundness`.
  * §3 **NC (a), the compiled part**: the wrong-claim program `*[0 [5 [1 [0 1]] [1 [1 0]]]]`, whose
    Nock value is `1`, with the claim `0`; its operands collide at seed `1` in every field
    (`collision_at_one`, `not_sepSeed_at_one`, `one_mem_pairBadSeeds`); the `generated` field holds
    for the WRONG claim (`wrongClaim_generated`: the field leaves the result free), and `primeField`
    at every `ZMod p`.

  Fixed-trace shape only; no interactive (`:966`) statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Lean Meta Elab Command

namespace Nock.RedTeam.Batch1400

/-! ## §1 The constant walk -/

/-- Field name of a primitive projection, `Type.field`. -/
def projName (env : Environment) (s : Name) (i : Nat) : Name :=
  match (getStructureFields env s)[i]? with
  | some f => s ++ f
  | none => s ++ Name.mkSimple s!"proj{i}"

/-- Constants and primitive projections occurring in `e`. -/
def readsOf (env : Environment) (e : Expr) : NameSet := Id.run do
  let mut acc : NameSet := {}
  for c in e.getUsedConstants do acc := acc.insert c
  -- primitive projections
  let mut stack : Array Expr := #[e]
  let mut out := acc
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    match x with
    | .proj s i b => out := out.insert (projName env s i); stack := stack.push b
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ => stack := stack.push t |>.push b
    | .forallE _ t b _ => stack := stack.push t |>.push b
    | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
    | .mdata _ b => stack := stack.push b
    | _ => pure ()
  return out

/-- The reads-walk from `root`: types and definition bodies, `Nock.*` only; theorem values are not
entered; inductive constructors are entered only at the root. -/
def readsWalk (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut exprs : Array Expr := #[ci.type]
    match ci with
    | .defnInfo d => exprs := exprs.push d.value
    | .inductInfo i =>
      if n == root then
        for c in i.ctors do
          if let some cc := env.find? c then exprs := exprs.push cc.type
    | _ => pure ()
    for e in exprs do
      for c in (readsOf env e).toList do
        if (`Nock).isPrefixOf c && !seen.contains c then
          if let some ci' := env.find? c then
            if !ci'.isThm then stack := stack.push c
          else
            -- a primitive-projection name (not a constant): record it
            seen := seen.insert c
  return seen

def pkgPrefixes : List Name :=
  [`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage,
   `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage,
   `Nock.NockVMROM.Thm54.SampledIOSameExecutionAssignment,
   `Nock.NockVMROM.Thm54.FiniteIO.FiniteIOStrategy]

def forbiddenLast : List String := ["strategy", "objects", "census", "records"]

def isPkgProj (n : Name) : Bool := pkgPrefixes.any fun p => p.isPrefixOf n && n != p

def isForbidden (n : Name) : Bool :=
  isPkgProj n && (forbiddenLast.contains (n.getString!) ||
    n == `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.sampled)

run_cmd do
  let env ← getEnv
  let tgt := `Nock.NockVMROM.Thm54.DeployedAcceptanceAt
  let old := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.OptimizedHistoricalAcceptanceAt
  let w := readsWalk env tgt
  let reads := (w.toList.filter isPkgProj).map toString
  let bad := w.toList.filter isForbidden
  logInfo m!"WALK DeployedAcceptanceAt: {w.size} names; package projections read ({reads.length}): {reads}"
  unless bad.isEmpty do
    throwError m!"DeployedAcceptanceAt reads a forbidden projection: {bad}"
  let w' := readsWalk env old
  let bad' := (w'.toList.filter isForbidden).map toString
  logInfo m!"WALK positive control OptimizedHistoricalAcceptanceAt: {w'.size} names; forbidden found: {bad'}"
  unless bad'.any (fun s => s.endsWith ".strategy") && bad'.any (fun s => s.endsWith ".sampled") do
    throwError m!"positive control failed: {bad'}"
  logInfo m!"WALK PASS: DeployedAcceptanceAt reads no strategy/objects/census/sampled/records; control fires"

/-! ## §2 The import walk -/

def closureOfMod (env : Environment) (m : Name) : NameSet := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:names.size] do idx := idx.insert names[i]! i
  let some p := idx.get? m | return {}
  let mut seen : NameSet := {}
  let mut stack : Array Name := (data[p]!.imports.map (·.module))
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    if let some i := idx.get? x then stack := stack ++ (data[i]!.imports.map (·.module))
  return seen

run_cmd do
  let env ← getEnv
  let stmt := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
  let low := closureOfMod env `Nock.NockVMROM.Thm54.P8Core.HostileSemanticSoundnessEv
  let high := closureOfMod env `Nock.NockVMROM.Thm54.HostileSemanticSoundness
  let rt := low.toList.filter fun x => (`Nock.RedTeam).isPrefixOf x
  logInfo m!"IMPORT-WALK P8Core.HostileSemanticSoundnessEv: closure {low.size}; statement {low.contains stmt}; RedTeam {rt.length}: {rt}"
  logInfo m!"IMPORT-WALK positive control Thm54.HostileSemanticSoundness: closure {high.size}; statement {high.contains stmt}"
  if low.contains stmt then throwError "P8Core module imports the statement file"
  unless high.contains stmt do throwError "positive control failed"
  unless rt.length ≤ 10 do throwError m!"RedTeam modules beyond the allowed 10: {rt}"

/-! ## §3 NC (a): the compiled part -/

open Nock Nock.NockVMROM.Thm54

def nA : Noun := .cell (.atom 0) (.atom 1)
def nB : Noun := .cell (.atom 1) (.atom 0)
/-- `[5 [1 nA] [1 nB]]`. -/
def wcFormula : Noun := .cell (.atom 5) (.cell (.cell (.atom 1) nA) (.cell (.atom 1) nB))
/-- The WRONG claim: Nock gives `1` (the operands differ), the claim records `0`. -/
def wrongClaim : P8PublicClaim := ⟨.atom 0, wcFormula, .atom 0⟩

theorem nA_ne_nB : nA ≠ nB := by decide

theorem wc_run : Nock.evalN 4 (.atom 0) wcFormula = some (.atom 1) := by decide

/-- The wrong claim does NOT hold: `evalN` is deterministic in fuel and returns `1`. -/
theorem wrongClaim_not_holds : ¬ wrongClaim.Holds := by
  rintro ⟨fuel, h⟩
  have h1 := Nock.evalN_mono (Nat.le_max_left fuel 4) h
  have h2 := Nock.evalN_mono (Nat.le_max_right fuel 4) wc_run
  change Nock.evalN _ (.atom 0) wcFormula = some (.atom 0) at h1
  rw [h1] at h2
  simp at h2

/-- The two operands' fingerprints collide at the seed `1`, in every field. -/
theorem collision_at_one {K : Type} [Field K] :
    GlobalCarryRecognizer.enc (1 : K) nA = GlobalCarryRecognizer.enc 1 nB := by
  ext
  · simp [GlobalCarryRecognizer.enc, nA, nB, Noun.leaves]
  · rfl
  · simp [GlobalCarryRecognizer.enc, nA, nB, NPR.listPoly, NPR.leafF, Noun.leafList, NPR.cpoly,
      Finset.sum_range_succ]

/-- … and as field nouns they differ (`0 ≠ 1`), so `1` is a bad seed of the pair. -/
theorem not_sepSeed_at_one {K : Type} [Field K] :
    ¬ GlobalCarryRecognizer.SepSeed (1 : K) nA nB := by
  intro h
  apply h
  · intro heq
    have := congrArg (fun x => x.1) heq
    simp [NPR.leafF, nA, nB, Noun.leafList] at this
  · exact GlobalCarryRecognizer.enc_eq_imp_fn_eq _ _ _ collision_at_one

theorem one_mem_pairBadSeeds {K : Type} [Field K] [Fintype K] [DecidableEq K] {Λ : ℕ}
    (hΛ : 2 ≤ Λ) : (1 : K) ∈ PreSeedCensus.pairBadSeeds (K := K) Λ [(nA, nB)] :=
  (PreSeedCensus.mem_pairBadSeeds_iff Λ _ 1).2
    ⟨(nA, nB), by simp, by simpa [nA, Noun.leaves] using hΛ, by simpa [nB, Noun.leaves] using hΛ,
      not_sepSeed_at_one⟩

/-- The generator's leaf bound of the wrong-claim program is `7`. -/
theorem wc_leafIs {K : Type} [Field K] :
    GeneratedField.LeafIs (K := K) 2 (.atom 0) wcFormula 7 := by
  simp only [wcFormula, nA, nB]
  gen_simp

/-- **The `generated` field holds for the WRONG claim** at every window `Λ ≥ 7`, at any field with
`1 < ringChar K` (the guarded run returns `1`; the field leaves the result free, as signed). -/
theorem wrongClaim_generated {K : Type} [Field K] (hK : 1 < ringChar K) (Λ : ℕ) (hΛ : 7 ≤ Λ) :
    GeneratedField.ClaimGenerated K wrongClaim Λ := by
  have he : (FieldEmbedding.evalGBy (ringChar K) 2 (.atom 0) wcFormula).isSome := by
    simp only [wcFormula, nA, nB]
    simp [FieldEmbedding.evalGBy, Noun.slot, Noun.tis, Noun.wut,
      FieldEmbedding.BoundedBy, hK]
  exact GeneratedField.generated_of (K := K) _ _ _ _ 2 2
    (GeneratedField.le_of_leafIs wc_leafIs hΛ) he

/-- `primeField` at every `ZMod p`. -/
theorem wrongClaim_primeField (p : ℕ) [Fact p.Prime] : GeneratedField.PrimeFieldElems (ZMod p) :=
  GeneratedField.primeFieldElems_zmod p

end Nock.RedTeam.Batch1400

#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_pinned
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_holdsMod
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_holdsMod_q
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.wrong_claim_rejected
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.wrong_record_rejected
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_ev
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_evalGBy_ev
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.hostileSemanticSoundness_holdsMod_ev
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.wrong_record_rejected_ev
#print axioms Nock.NockVMROM.Thm54.HostileSemanticSoundness.one_wrong_record_rejected_ev
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompilesHostile
#print axioms Nock.RedTeam.Batch1400.wrongClaim_not_holds
#print axioms Nock.RedTeam.Batch1400.collision_at_one
#print axioms Nock.RedTeam.Batch1400.not_sepSeed_at_one
#print axioms Nock.RedTeam.Batch1400.one_mem_pairBadSeeds
#print axioms Nock.RedTeam.Batch1400.wrongClaim_generated
