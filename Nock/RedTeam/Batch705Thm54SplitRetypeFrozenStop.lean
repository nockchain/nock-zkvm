/-
  Nock/RedTeam/Batch705Thm54SplitRetypeFrozenStop.lean

`FrozenClosure.fingerprint` of an inductive mixes its constructor types, and the
    constructor's type reads `BareSemanticSupport` (field `semantics`). The split removes that
    field and adds `skeleton` / `publicClaim_eq`, so the constructor type, hence the fingerprint,
    necessarily moves. The plan's "none of the 14 pinned conjuncts changes form" is true and beside the point: the closure pins
    the structure's own constructor.
  * Measured below (positive control): the live fingerprint is recomputed with
    `FrozenClosure`'s algorithm and equals the pin, and the constructor reads
    `BareSemanticSupport`.
  `BindsAtCoin` needs `λ` as an argument (threaded since the 28th; the plan's §1 text omits it).

  Nothing in production is edited.

-/
import Lean
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.RedTeam.Batch531Thm54MemFirstAndReady

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch705

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment

/-! ## §A — the frontier fingerprint the split must move (measured, positive control) -/

open Lean in
/-- `FrozenClosure.fingerprint`'s hash, re-implemented verbatim for an inductive
(`#[type] ++ ctorTypes`, `mixHash` from `17`). -/
def inductiveFingerprint (env : Environment) (n : Name) : Option UInt64 := do
  let ci ← env.find? n
  let ctors := match ci with
    | .inductInfo iv => iv.ctors.foldl (init := #[]) fun acc c =>
        match env.find? c with
        | some cci => acc.push cci.type
        | none => acc
    | _ => #[]
  let es := #[ci.type] ++ ctors
  return es.foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash

/- §A, re-measured at the authorized retype. It now asserts that the real retype reproduces the split
replica's fingerprint `10043048227177245424`, with 3 ctor fields and no `BareSemanticSupport`. -/
open Lean in
run_cmd do
  let env ← getEnv
  let n := ``ProductionP8Containment.ProductionStrategy
  let some h := inductiveFingerprint env n | throwError "ProductionStrategy missing"
  unless h == 10043048227177245424 do
    throwError m!"live fingerprint {h} ≠ split replica 10043048227177245424"
  let some (.ctorInfo cv) := env.find? ``ProductionP8Containment.ProductionStrategy.mk
    | throwError "ProductionStrategy.mk missing"
  if cv.type.getUsedConstants.contains ``ProductionP8Containment.BareSemanticSupport then
    throwError "ctor still reads BareSemanticSupport"
  unless cv.numFields == 3 do
    throwError m!"ctor has {cv.numFields} fields, expected 3 (verifier, skeleton, publicClaim_eq)"
  logInfo m!"A ProductionStrategy fingerprint {h} = split replica; ctor (3 fields) does not read BareSemanticSupport"



end Nock.RedTeam.Batch705
