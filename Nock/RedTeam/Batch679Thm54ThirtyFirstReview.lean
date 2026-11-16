/-
  Nock/RedTeam/Batch679Thm54ThirtyFirstReview.lean

* **Check 10.**  The twelve added names' live fingerprints equal the pins (`pins_match`).
    Own control: a verbatim replica of `expInitGate` reproduces its pinned fingerprint
    `906629591434476874` bit for bit; the signature-preserving perturbation `isFirst · (S + 0)`
    changes it (`control_fires`) while the type is unchanged.

  -- the paper
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.FamilyMemoryRows
import Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch501Thm54MemoryTopology

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command Meta

namespace Nock.RedTeam.Batch679

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open scoped Polynomial

noncomputable section

/-! ## Check 4 -/

section Vacuity
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K] {hOrb : ℕ}

theorem rowExpTerm_eq_zero_iff (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F) (Qm : Fin P.memoryChip.rap.w → Polynomial F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    FamilyMemoryRows.rowExpTerm P c Qm i = 0 ↔
      c.2.1.1 = 0 ∨ (memoryBaseEnvAt P c Qm i).trace reqIdxCol = 0 := by
  unfold FamilyMemoryRows.rowExpTerm
  rw [mul_eq_zero, pow_eq_zero_iff (by norm_num : (9 : ℕ) ≠ 0),
    map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective]
  tauto

/-- The honest tenth slot is at least `1` on every record row. -/
theorem reqIdxNat_pos {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    (R : PlusIOSegmentedFamily F K) (pub : MemoryTable.Pub K)
    (h : pub.st = .read_root ∨ pub.st = .verify_child) :
    1 ≤ OptimizedMemorySemanticRealization.reqIdxNat R pub := by
  unfold OptimizedMemorySemanticRealization.reqIdxNat
  rw [if_pos h]
  unfold RecordCarrier.honestExp
  omega

end Vacuity

end

/-! ## Check 3 — reach -/

partial def reach (env : Environment) (roots : Array Name) (stop : Name → Bool) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if stop n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

run_cmd do
  let env ← getEnv
  let stop : Name → Bool := fun n => !(`Nock).isPrefixOf n
  let roots := #[``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76,
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package]
  let forbidden := #[``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_vmem_at,
    ``Nock.NockVMROM.Thm54.FamilyMemoryRows.deployed_row_interV_at,
    ``Nock.NockVMROM.Thm54.FamilyMemoryRows.expShiftInputs,
    ``Nock.NockVMROM.Thm54.FamilyMemoryRows.rowExpTerm]
  let positive := #[``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxCol,
    ``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.computeExpGates,
    ``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxRLCTerm,
    ``Nock.NockVMROM.Thm54.RecordCarrier.withExp]
  let carriers : Array Name := #[`Nock.RedTeam.Batch490Thm54TopologyAssembly,
    `Nock.RedTeam.Batch501Thm54MemoryTopology]
  for r in roots do
    let cl := reach env #[r] stop
    for p in positive do
      unless cl.contains p do throwError m!"positive control: {p} not reached from {r}"
    for f in forbidden do
      if cl.contains f then throwError m!"{f} reached from {r}"
    let hits := cl.toArray.filter fun n =>
      match env.getModuleFor? n with
      | some m => carriers.contains m
      | none => false
    unless hits.isEmpty do throwError m!"Batch490/501 constants reached from {r}: {hits}"
    logInfo m!"{r}: closure {cl.size}; shifted-β lemmas and Batch490/501 not reached; carrier names reached"

/-! ## Check 10 — pins and an own control -/

/-- Verbatim replica of `expInitGate` (binders written as in the source: the unused `[Field F]`
is part of its signature). -/
def gateA {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.var .traceCur 11) (.var .traceCur computeExpCol)

/-- Signature-preserving perturbation: `isFirst · (S + 0)`. -/
def gateB {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.var .traceCur 11) (.add (.var .traceCur computeExpCol) (.const 0))

def meaningExprs (env : Environment) (n : Name) : Array Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let base := #[ci.type]
    match ci with
    | .thmInfo _ => base
    | .axiomInfo _ => base
    | _ => match ci.value? (allowOpaque := true) with
           | some v => base.push v
           | none => base

def fp (env : Environment) (n : Name) : UInt64 :=
  (meaningExprs env n).foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash

run_cmd do
  let env ← getEnv
  let pins : Array (Name × UInt64) := #[
    (``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.arityForm, 17465734203661140776),
    (``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.computeExpCol, 16656362723618729205),
    (``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.computeExpGates, 17202374157891817113),
    (``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.expInitGate, 906629591434476874),
    (``Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal.expStepGate, 8598724804523106772),
    (``Nock.NockVMROM.Thm54.OptimizedComputeSubstitution.sampledSlotE, 8339894589683189937),
    (``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.poleSourceMixed, 3905162607030239616),
    (``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.recordRLC, 15491206942659154479),
    (``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxCol, 16225661998323485280),
    (``Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis.reqIdxRLCTerm, 11241788103090626959),
    (``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.hostileInterRecords, 7508517569764433093),
    (``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.hostileRecords, 15352673378135290329)]
  for (n, h) in pins do
    let h' := fp env n
    unless h' == h do throwError m!"live fingerprint of {n} is {h'}, pinned {h}"
  logInfo "pins_match: the twelve added names' live fingerprints equal frozen-pins.json"
  let a := fp env ``Nock.RedTeam.Batch679.gateA
  let b := fp env ``Nock.RedTeam.Batch679.gateB
  logInfo m!"control: gateA {a} (pinned expInitGate 906629591434476874), gateB {b}"
  unless a == 906629591434476874 do throwError "replica does not reproduce expInitGate's fingerprint"
  unless a != b do throwError "control_fires failed"
  let some ca := env.find? ``Nock.RedTeam.Batch679.gateA | throwError "no gateA"
  let some cb := env.find? ``Nock.RedTeam.Batch679.gateB | throwError "no gateB"
  unless ca.type.hash == cb.type.hash do throwError "control_types_equal failed"
  logInfo "control_fires, control_types_equal"

end Nock.RedTeam.Batch679
