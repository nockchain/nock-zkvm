import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.P8Core.PartAStaged12
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1443Thm54PartAhATStop.lean

  **The measured reason `hAT` (the `p8`
  conjunct of the parallel target) does not transport.**

  The current target's `p8` conjunct (the claim holds under `evalN`) is proved by
  `PlacementA.holds_of_acceptance_evOnly`, whose FIRST hypothesis is
  `DeployedAcceptanceAt P c Qc Qm` — the landed 303-wide compute chip AND the landed memory chip
  at ONE eleven-coin tuple `c`, with the memory walk read at `alphaM c.1` (memory slot 3), and whose
  second is `c ∉ optimizedFailureEventEv P …` with the walk summands 7 and 10 lifted at that same
  `alphaM`.  At the parallel package the compute chip (309, un-hosted) is read at `forget12 c`
  (timestamp `α`) and the memory chip at `walkView11 c` (walk coin `αW`):

  * §A `views_differ`: when `αW ≠ α` those are two different landed tuples, so no single landed
    tuple carries both chips' reads (and the consumed event prices summands 7 / 10 at `αW`, not at
    the landed tuple's `alphaM`);
  * §B the reach census of the landed chain (`#eval`, proof terms included,
    `value? (allowOpaque := true)`): how many declarations in the transitive closure of
    `holds_of_acceptance_evOnly` take `DeployedAcceptanceAt`, take a landed memory-chip
    satisfaction, take a landed compute-chip satisfaction — every one of them is stated at the
    single-tuple landed object and would need a genuine re-proof at the split coin / 309 chip.
    Positive control: the root itself takes `DeployedAcceptanceAt`.
-/

set_option autoImplicit false

namespace Nock.RedTeam.Batch1443

open Nock Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.PartA12

/-! ## §A. The two chips read two different landed tuples -/

theorem views_differ {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple12 K F) (h : walkAlphaOf c ≠ alphaM c.1) :
    walkView11 c ≠ forget12 c := by
  intro he
  apply h
  have := congrArg (fun t : OptimizedProductionChallengeTuple K F => alphaM t.1) he
  exact this

/-- At `αW = α` they coincide (the landed chain then applies verbatim, through L3's
`memoryChipAt12_satisfies_iff`). -/
theorem views_eq {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple12 K F) (h : walkAlphaOf c = alphaM c.1) :
    walkView11 c = forget12 c := by
  rcases c with ⟨⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩, ⟨⟨a5, a6⟩, ⟨r, ⟨i, l, w⟩⟩⟩⟩
  simp only [walkAlphaOf, alphaM] at h
  subst h
  rfl

/-! ## §B. The reach census -/

open Lean in
/-- Transitive constant closure (types and values, proofs included), restricted to `Nock`. -/
def reach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  let mut fuel := 10000000
  while stack.size > 0 && fuel > 0 do
    fuel := fuel - 1
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut es := #[ci.type]
    if let some v := ci.value? (allowOpaque := true) then es := es.push v
    if let .inductInfo ii := ci then
      for ctor in ii.ctors do stack := stack.push ctor
    for e in es do
      for c in e.getUsedConstants do
        if (`Nock).isPrefixOf c && !seen.contains c then stack := stack.push c
  return seen

open Lean in
def mentions (e : Expr) (n : Name) : Bool := (e.find? fun x => x.isConstOf n).isSome

open Lean in
/-- A satisfaction hypothesis at a chip built by one of `chips`. -/
def takesSat (t : Expr) (chips : List Name) : Bool :=
  (t.find? fun x => x.isAppOf `Nock.Framework.RAP.SatisfiesWithPreprocessing &&
    x.getAppArgs.toList.any fun a => chips.any fun c => mentions a c).isSome

open Lean in
run_cmd do
  let env ← getEnv
  let root := `Nock.NockVMROM.Thm54.PlacementA.holds_of_acceptance_evOnly
  let da := `Nock.NockVMROM.Thm54.DeployedAcceptanceAt
  let memChips := [`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memoryChipAt,
    `Nock.NockVMROM.Thm54.DeployedChipFamily.memoryChipAt]
  let cmpChips := [`Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.computeChipAt,
    `Nock.NockVMROM.Thm54.DeployedChipFamily.computeChipAt]
  let some rci := env.find? root | throwError "Batch1443: root missing"
  unless mentions rci.type da do throwError "Batch1443 control: root does not take DeployedAcceptanceAt"
  let s := reach env root
  let mut nDA := 0
  let mut nMem := 0
  let mut nCmp := 0
  for n in s.toList do
    let some ci := env.find? n | continue
    unless ci matches .thmInfo _ do continue
    if mentions ci.type da then nDA := nDA + 1
    if takesSat ci.type memChips then nMem := nMem + 1
    if takesSat ci.type cmpChips then nCmp := nCmp + 1
  unless nDA > 0 && nMem > 0 && nCmp > 0 do throwError "Batch1443: census empty"
  logInfo m!"Batch1443 REACH holds_of_acceptance_evOnly: closure {s.size}; theorems taking \
    DeployedAcceptanceAt {nDA}, a landed memory-chip satisfaction {nMem}, a landed compute-chip \
    satisfaction {nCmp}"

end Nock.RedTeam.Batch1443

#print axioms Nock.RedTeam.Batch1443.views_differ
#print axioms Nock.RedTeam.Batch1443.views_eq
