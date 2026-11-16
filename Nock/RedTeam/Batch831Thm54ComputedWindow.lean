/-
  Nock/RedTeam/Batch831Thm54ComputedWindow.lean

  * **(A) Reach check** (`value? Positive controls: the instrument finds each probe where it is known to be.
  * **(C) Non-vacuity.**  A concrete genuine tree (`[[0 1] [1 5]]` on subject `7`) satisfies every
    hypothesis of `genuine_rows_le_programLeafBound` together; the theorem returns the honest
    result `[7 5]`.
  * **(D) Negative control (the alignment has teeth).**  The same rows with a forged root
    evaluation are NOT genuine: alignment forces the honest result (`forged_root_not_genuine`).
  * **(E) The obstruction, landed.**
-/
import Lean
import Nock.NockVMROM.Thm54.ComputedWindow
import Nock.NockVMROM.Thm54.ComputedWindowJoin
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.AxisBridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch831

open Lean Elab Command
open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

/-! ## (A) Reach check -/

partial def reachNames (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !((`Nock).isPrefixOf n) then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

def STMT : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement

def probes : Array Name := #[
  PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem,
  PKG ++ `OptimizedSameProblemAt,
  PKG ++ `OptimizedHistoricalAcceptanceAt.p8,
  STMT,
  ``Nock.MemoryTable.interV,
  ``Nock.MemoryTable.Vmem]

def laneNs : Name := `Nock.NockVMROM.Thm54.ComputedWindow

def delivered (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if laneNs.isPrefixOf n && !n.isInternal then out := out.push n
  return out

run_cmd do
  let env ← getEnv
  for p in probes do
    unless env.contains p do throwError m!"probe name missing: {p}"
  -- positive controls: the instrument finds every probe where it is known to be
  let ctl : List (Name × Name) := [
    (``OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package, STMT),
    (``OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
      PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem),
    (``OptimizedFullStrictNockVMROMPackage.optimizedHistoricalAcceptanceAt_iff,
      PKG ++ `OptimizedHistoricalAcceptanceAt.p8),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedSameProblemAt),
    (``Nock.AxisBridge.wf_memwalk_of_memAIR, ``Nock.MemoryTable.interV),
    (``Nock.AxisBridge.wf_memwalk_of_memAIR, ``Nock.MemoryTable.Vmem)]
  for (r, p) in ctl do
    unless (reachNames env #[r]).contains p do
      throwError m!"positive control failed: {r} does not reach {p}"
  logInfo m!"Batch831 (A): {ctl.length} positive controls pass"
  let ds := delivered env
  unless ds.size ≥ 40 do throwError m!"delivered set too small: {ds.size}"
  let mut bad : Array (Name × Name) := #[]
  for d in ds do
    let r := reachNames env #[d]
    for p in probes do
      if r.contains p then bad := bad.push (d, p)
  unless bad.isEmpty do throwError m!"Batch831 (A): a delivered constant reaches a probe: {bad}"
  logInfo m!"Batch831 (A): {ds.size} ComputedWindow constants reach none of {probes.size} probes"
  let keys : List Name := [``genuine_aligned, ``genuine_rows_le_programLeafBound,
    ``decodedSkeleton_aligned, ``computedWindow_row, ``honestCall_kid, ``computedWindow_tree,
    ``honestCall_inputs_le, ``s3_pair_nouns_le_window3, ``decoded_le_window3,
    ``tailCons_right_le, ``formulaCons_right_le, ``join_kidInputs, ``join_rowOutput,
    ``join_genuine_node, ``sizeWindow_of_le, ``step_align, ``s3_pairs_separated,
    ``sepSeed_of_guard]
  for k in keys do
    unless ds.contains k do throwError m!"key theorem missing from the delivered set: {k}"
  unless (reachNames env #[``decodedSkeleton_aligned]).contains
      ``Nock.NockVMROM.Thm54.StrategyOfTraces.mapComputeJoinInFuel do
    throwError "positive control failed: decodedSkeleton_aligned does not reach the join"
  unless (reachNames env #[``genuine_rows_le_programLeafBound]).contains
      ``Nock.NockVMROM.Thm54.TraceGen.programLeafBound do
    throwError "positive control failed: the window theorem does not reach programLeafBound"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axBad : Array (Name × Name) := #[]
  for d in ds do
    let axs ← liftCoreM (Lean.collectAxioms d)
    for a in axs do
      unless allowed.contains a do axBad := axBad.push (d, a)
  unless axBad.isEmpty do throwError m!"Batch831 (B): non-standard axiom: {axBad}"
  logInfo m!"Batch831 (B): {ds.size} constants use only propext / Classical.choice / Quot.sound"

/-! ## (C) Non-vacuity: a concrete genuine tree -/

def S0 : Noun := .atom 7
def fL : Noun := .cell (.atom 0) (.atom 1)
def fR : Noun := .cell (.atom 1) (.atom 5)
def F0 : Noun := .cell fL fR
def R0 : Noun := .cell (.atom 7) (.atom 5)

def rowL : ComputeRowSkeleton := genSkelOp0 S0 fL (.atom 0) (.atom 1) (.atom 7) 1
def rowR : ComputeRowSkeleton := genSkelOp1 S0 fR (.atom 5) (.atom 1)
def rowRoot (e : Noun) : ComputeRowSkeleton :=
  { genSkelCons S0 fL fR (.atom 7) (.atom 5) with evaluation := e }

def treeAt (e : Noun) : NTree ComputeRowSkeleton :=
  .node (rowRoot e) [.node rowL [], .node rowR []]

theorem genuine_example : GenuineSkel (treeAt R0) := by
  have gL : GenuineSkel (.node rowL []) :=
    .node ⟨1, rfl⟩ (by simp [KidInputs, rowL, genSkelOp0])
      (by simp [RowOutput, rowL, genSkelOp0, op0Axis, S0, fL, Noun.slot]) (by simp)
  have gR : GenuineSkel (.node rowR []) :=
    .node ⟨.atom 5, rfl⟩ (by simp [KidInputs, rowR, genSkelOp1])
      (by simp [RowOutput, rowR, genSkelOp1, fR, tl, StrategyOfTraces.nounTail]) (by simp)
  refine .node ⟨.atom 0, .atom 1, fR, rfl⟩ ?_ ?_ ?_
  · simp [KidInputs, rowRoot, rowL, rowR, genSkelCons, genSkelOp0, genSkelOp1, NTree.label,
      hd, tl, StrategyOfTraces.nounHead, StrategyOfTraces.nounTail, fL]
  · simp [RowOutput, rowRoot, rowL, rowR, genSkelCons, genSkelOp0, genSkelOp1, NTree.label, R0]
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl
    · exact gL
    · exact gR

theorem evalRom_example : evalRom 3 S0 F0 = some R0 := by
  simp [evalRom, S0, F0, fL, fR, R0, Noun.slot]

/-- **(C)** Every hypothesis of Theorem 1's window form holds at once on a concrete program, and
the theorem returns the honest result. -/
theorem nonvacuous_example {K : Type} [Field K] :
    R0 = (treeAt R0).label.evaluation ∧
      Aligned (K := K) (treeAt R0) (airReorder (romTree (K := K) evalRom_example)) ∧
      ∀ u, InTree (treeAt R0) u →
        RowNounsLe (programLeafBound (airReorder (romTree (K := K) evalRom_example))) u.label :=
  genuine_rows_le_programLeafBound (romTree_spec (K := K) evalRom_example) genuine_example
    rfl rfl

/-! ## (D) Negative control: a forged root evaluation is rejected by the alignment -/

theorem forged_root_not_genuine {K : Type} [Field K] :
    ¬ GenuineSkel (treeAt (.atom 42)) := by
  intro h
  have := (genuine_rows_le_programLeafBound (K := K) (romTree_spec (K := K) evalRom_example) h
    rfl rfl).1
  simp [treeAt, rowRoot, R0, NTree.label] at this

/-! ## (E) The obstruction: no uniform `≤ c·M` bound on honest computed nouns -/

def chain : ℕ → Noun
  | 0 => .cell (.atom 0) (.atom 1)
  | k + 1 => .cell (.cell (.atom 0) (.atom 1)) (chain k)

def rep (S : Noun) : ℕ → Noun
  | 0 => S
  | k + 1 => .cell S (rep S k)

theorem chain_leaves (k : ℕ) : (chain k).leaves = 2 * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [chain, Noun.leaves, ih]; ring

theorem rep_leaves (S : Noun) (k : ℕ) : (rep S k).leaves = (k + 1) * S.leaves := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp only [rep, Noun.leaves, ih]; ring

theorem evalN_chain (S : Noun) :
    ∀ k fuel, k + 2 ≤ fuel → evalN fuel S (chain k) = some (rep S k) := by
  intro k
  induction k with
  | zero =>
    intro fuel h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [chain, rep, evalN, Noun.slot]
  | succ k ih =>
    intro fuel h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have := ih (g + 1) (by omega)
    simp [chain, rep, evalN, Noun.slot, this]

/-- **(E)** For every `c` there is an honest evaluation whose result has more than
`c·(leaves subject + leaves formula)` leaves (probe `LeafBound.honest_result_exceeds`). -/
theorem honest_result_exceeds (c L : ℕ) (S : Noun) (hS : S.leaves = L) (hL : 4 * c + 4 ≤ L) :
    ∃ k r, evalN (k + 2) S (chain k) = some r ∧
      c * (S.leaves + (chain k).leaves) < r.leaves := by
  refine ⟨4 * c + 3, rep S (4 * c + 3), evalN_chain S _ _ le_rfl, ?_⟩
  rw [rep_leaves, chain_leaves, hS]
  nlinarith

end Nock.RedTeam.Batch831

#print axioms Nock.RedTeam.Batch831.nonvacuous_example
#print axioms Nock.RedTeam.Batch831.forged_root_not_genuine
#print axioms Nock.RedTeam.Batch831.honest_result_exceeds
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.genuine_aligned
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.decodedSkeleton_aligned
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.computedWindow_row
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.honestCall_kid
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.s3_pair_nouns_le_window3
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.join_genuine_node
#print axioms Nock.NockVMROM.Thm54.ComputedWindow.s3_pairs_separated
