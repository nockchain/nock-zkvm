/-
  Nock/RedTeam/Batch1500Thm54StandaloneCensus.lean

  1. **Read-set census (fails the build if violated).**  A proof-term walker (types AND values,
     theorems through `value? (allowOpaque := true)`, every `Nock.*` constant) from `chipsOf`,
     `AcceptsV`, `StagedV`, `pubC`, `currentMemFamily`: no field projection of either package
     structure (`OptimizedStrictNockVMROMPackage`, `OptimizedFullStrictNockVMROMPackage`) is
     reached, and no field of `VerifierData.Checks` is reached (the chips read no check).
     **Positive control:** the same walker from `Unhosted309.pkgComputeChipAt309` and
     `Pkg12.memoryChipAt12` reaches package fields (asserted, else the build fails).
     The reached `VerifierData` / `Messages` fields are logged.
  2. **Generic in the memory chip.**  `chipsOf_snd`: at every `MemChipFamily`, the memory chip is
     the family's constructor at `(V, memMsg0, requests c, memMsg2 c, c)` (`rfl`) — nothing of the
     current memory chip is assumed by the generic layer; `requests_shared`: both chips read the
     one value `m.requests c` (compute publics `6..8`; the family's argument).
  3. **The package is an instance.**  `chipsOf_ofPackage` re-exported with `#print axioms`.
-/
import Lean
import Nock.NockVMROM.Thm54.StandaloneVerifierData
import Nock.NockVMROM.Thm54.StandaloneVerifierPackage
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1500

open Lean Meta Elab Command
open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.StandaloneVerifier
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.CoordinateBasis

/-! ## 1. The read-set census -/

/-- Proof-term closure over `Nock.*` constants (types and values, theorems included). -/
partial def reachSV (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots.toArray
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut es : Array Expr := #[ci.type]
      if let some v := ci.value? (allowOpaque := true) then es := es.push v
      for e in es do
        for c in e.getUsedConstants do
          if (`Nock).isPrefixOf c && !seen.contains c then todo := todo.push c
  return seen

def pkgStructsSV : List Name := [
  `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage,
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage]

/-- Field projections of structure `st` reached by `s`. -/
def fieldsHit (env : Environment) (s : NameSet) (st : Name) : List Name :=
  (getStructureFields env st).toList.filter fun f => s.contains (st ++ f)

def svRoots : List Name := [
  ``StandaloneVerifier.chipsOf, ``StandaloneVerifier.AcceptsV, ``StandaloneVerifier.StagedV,
  ``StandaloneVerifier.pubC, ``StandaloneVerifier.currentMemFamily,
  ``StandaloneVerifier.pubMCurrent]

run_cmd do
  let env ← getEnv
  let s := reachSV env svRoots
  -- (a) no package field
  for st in pkgStructsSV do
    unless isStructure env st do throwError "census: {st} is not a structure"
    let hit := fieldsHit env s st
    unless hit.isEmpty do
      throwError "census FAILED: the standalone chips reach package fields of {st}: {hit}"
  -- (b) no check
  let chk := fieldsHit env s ``StandaloneVerifier.VerifierData.Checks
  unless chk.isEmpty do
    throwError "census FAILED: the standalone chips reach verifier checks: {chk}"
  -- report the V / m fields read
  let vf := fieldsHit env s ``StandaloneVerifier.VerifierData
  let mf := fieldsHit env s ``StandaloneVerifier.Messages
  logInfo m!"standalone census: closure {s.size}; no package field, no check reached.\n  VerifierData fields read: {vf}\n  Messages fields read: {mf}"
  -- positive control: the package chips DO reach package fields
  for root in [``Unhosted309.pkgComputeChipAt309, ``Pkg12.memoryChipAt12] do
    let s' := reachSV env [root]
    let hits := pkgStructsSV.flatMap (fieldsHit env s')
    if hits.isEmpty then
      throwError "census positive control FAILED: {root} reaches no package field"
    logInfo m!"positive control {root}: package fields reached {hits}"

/-! ## 2. Generic in the memory chip; `requests` shared -/

section Generic

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K] {h : ℕ}

/-- At every memory family the memory chip is the family's constructor (no current-chip
internals in the generic layer). -/
theorem chipsOf_snd (MF : MemChipFamily F K h) (V : VerifierData F K h) (m : Messages F K MF)
    (c : Tuple12 K F) :
    (chipsOf V m c).2 = MF.chip V m.memMsg0 (m.requests c) (m.memMsg2 c) c := rfl

/-- The compute chip reads `requests c` at publics `6..8`, the value handed to the memory family. -/
theorem requests_shared (MF : MemChipFamily F K h) (V : VerifierData F K h) (m : Messages F K MF)
    (c : Tuple12 K F) (k : Fin 3) :
    pubC V m c (6 + (k : ℕ)) = coord V.basis (m.requests c) k := by
  unfold pubC
  rw [dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp)

/-- At the current family, the memory chip's publics `12..14` are `requests c`, too. -/
theorem requests_shared_current (V : VerifierData F K h) (rest : ℕ → F) (r s : K) (k : Fin 3) :
    pubMCurrent V rest r s (12 + (k : ℕ)) = coord V.basis r k := by
  unfold pubMCurrent
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp)

end Generic

/-! ## 3. The package is an instance -/

#check @StandaloneVerifier.chipsOf_ofPackage
#print axioms StandaloneVerifier.chipsOf_ofPackage
#print axioms StandaloneVerifier.chipsOf_ofPackage_traces
#print axioms StandaloneVerifier.msgsOfTraces_staged
#print axioms chipsOf_snd
#print axioms requests_shared
#print axioms requests_shared_current

end Nock.RedTeam.Batch1500
