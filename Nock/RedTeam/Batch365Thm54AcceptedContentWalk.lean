/-
  Nock/RedTeam/Batch365Thm54AcceptedContentWalk.lean

  **Statement walk.**  The restated spine
  `` `ProductionP8AcceptedContent.lean::accepted_outside_failureUnion_content` ``
  has a *type* that reaches none of `computeTableRAP`, `SixRAPSatisfy`,
  `RAP.Satisfies`.  Positive control: the same walk on the original
  `` `ProductionP8Containment.lean::accepted_outside_failureUnion` ``
  (via `Accepts`) does reach `SixRAPSatisfy`.

  Instrument: `ci.type.getUsedConstants` plus values of `Nock.*` defs
  (`value? (allowOpaque := true)`), named `reachSet` (Mathlib owns
  `closure`).
-/
import Lean
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent

set_option autoImplicit false

namespace Nock.RedTeam.Batch365

open Lean Meta Elab Command
open Nock.NockVMROM.Thm54.ProductionP8Containment

/-- Direct constants of a declaration's type. -/
def typeDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- Direct constants of a declaration's value (defs/theorems). -/
def valueDirect (env : Environment) (root : Name) : Array Name :=
  match env.find? root with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  | none => #[]

/-- Transitive `Nock.*` constants reachable from a root's *statement*
(type), entering definition values so `Accepts` unfolds. -/
def reachSet (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := typeDirect env root
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if (`Nock).isPrefixOf c then
      for d in typeDirect env c do
        unless seen.contains d do stack := stack.push d
      for d in valueDirect env c do
        unless seen.contains d do stack := stack.push d
  return seen

def FORBIDDEN_SUFFIXES : List String :=
  ["computeTableRAP", "SixRAPSatisfy", "RAP.Satisfies"]

def nameHasSuffix (n : Name) (suf : String) : Bool :=
  n.toString.endsWith suf

def reachHasSuffix (s : Std.HashSet Name) (suf : String) : Bool :=
  Id.run do
    for n in s do
      if nameHasSuffix n suf then return true
    return false

def CONTENT : Name :=
  ``Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion_content

def ORIGINAL : Name :=
  ``Nock.NockVMROM.Thm54.ProductionP8Containment.accepted_outside_failureUnion

def ACCEPTS : Name :=
  ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.Accepts

/-- The original `Accepts` expansion names the three forbidden constants
in its *statement*. -/
def IFF_EIGHT : Name :=
  ``Nock.NockVMROM.Thm54.ProductionRawVerifier.Message.verifierChecks_iff_eight_segmented_families

run_cmd do
  let env ← getEnv
  unless (env.find? CONTENT).isSome do
    throwError m!"missing {CONTENT}"
  unless (env.find? IFF_EIGHT).isSome do
    throwError m!"missing {IFF_EIGHT}"
  let rContent := reachSet env CONTENT
  let rOrig := reachSet env ORIGINAL
  let rIff := reachSet env IFF_EIGHT
  -- restated spine's statement reaches none of the three names
  for suf in FORBIDDEN_SUFFIXES do
    if reachHasSuffix rContent suf then
      throwError m!"content spine statement reaches forbidden suffix {suf}"
  -- positive control: the eight-family iff *statement* names them
  unless reachHasSuffix rIff "computeTableRAP" do
    throwError "positive control failed: iff statement does not reach computeTableRAP"
  unless reachHasSuffix rIff "SixRAPSatisfy" || reachHasSuffix rIff "Satisfies" do
    throwError "positive control failed: iff statement does not reach SixRAPSatisfy/Satisfies"
  unless rOrig.contains ACCEPTS do
    throwError "original statement does not mention Accepts"
  unless rContent.contains ``Nock.NockVMROM.Thm54.ProductionP8Containment.AcceptedContent do
    throwError "content spine statement does not mention AcceptedContent"
  logInfo m!"Batch365 walk: content reach={rContent.size} (no computeTableRAP / SixRAPSatisfy / RAP.Satisfies); original names Accepts; verifierChecks_iff reaches computeTableRAP/Satisfies (positive control)"

end Nock.RedTeam.Batch365
