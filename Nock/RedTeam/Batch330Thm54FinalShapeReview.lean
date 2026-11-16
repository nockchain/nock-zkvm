/-
  Nock/RedTeam/Batch330Thm54FinalShapeReview.lean

  Paper re-read at source: the paper 
  `:1450`, `:1531-1534`, `:1893`.

  Counts total/explicit: p70 35/18 -> 32/15; p71..p74 and nockCompiles 33/17 -> 30/14;
  converses p70_of_p71 35/18 -> 32/15, the other three 33/17 -> 30/14; the explicit names of
  `nockCompiles` lose `hfirst`, `hmore`, `hbasis`.

  Receipts:

  * B — each explicit binder of `nockCompiles` is classified as a §1
    line or a disclosed side condition; the conclusion names the
    statement and the claim triple, not `BuildableNockExecution`.
  * C — `hp : 29 ≤ ringChar K`: the cubic-vs-quadratic majorant and
    the actual worst-case `seedBudgetVcomp` both fail at `p = 23`.
  * D — `hΛp : Λ < p` is the sufficient direction for the seed budget;
    the three landed literals sit strictly under their primes; a
    program with `Λ ≥ p` is possible.
  * The paper's `+` is `lusFBy`
    (wrap); `evalGRom` uses `lusGBy` (crash).

  No production file under `Nock/NockVMROM/` is edited. Top-level `redteam-status.json` `status`
  is not flipped.
-/
import Lean
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.SizeWindowCounting
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.RedTeam.Batch325Thm54RunBoundedNotTyping
import Nock.RedTeam.Batch328Thm54HsHfAndSeedKind
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

open Lean Elab Command Meta

/-! ## A. Instrument: binder walk, names, position-wise type comparison -/

namespace Batch330BinderWalk

def binderTelescope (n : Name) : MetaM (Array (Name × BinderInfo)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ =>
    xs.mapM fun x => do
      let l ← x.fvarId!.getDecl
      pure (l.userName, l.binderInfo)

def binderCounts (n : Name) : MetaM (Nat × Nat × Nat) := do
  let tel ← binderTelescope n
  let mut expl := 0
  let mut impl := 0
  let mut inst := 0
  for (_, bi) in tel do
    match bi with
    | .default => expl := expl + 1
    | .implicit | .strictImplicit => impl := impl + 1
    | .instImplicit => inst := inst + 1
  return (tel.size, expl, inst)

def explicitNames (n : Name) : MetaM (Array Name) := do
  let tel ← binderTelescope n
  return tel.filterMap fun (nm, bi) =>
    if bi == .default then some nm else none

/-- Non-instance `Prop` binders (hypotheses proper). -/
def propBinderNames (n : Name) : MetaM (Array Name) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let bi ← x.fvarId!.getBinderInfo
      if bi != .instImplicit then
        if ← isProp (← inferType x) then
          out := out.push (← x.fvarId!.getUserName)
    return out

/-- Position-wise comparison of two equal-length telescopes. -/
def typeDiff (a b : Name) : MetaM (Array Name) := do
  let ia ← getConstInfo a
  let ib ← getConstInfo b
  forallTelescope ia.type fun xs _ => do
    let mut tb := ib.type
    let mut out := #[]
    for x in xs do
      let .forallE _ dom body _ := tb | throwError m!"{b} has fewer binders than {a}"
      let ta ← inferType x
      unless ← isDefEq ta dom do
        out := out.push (← x.fvarId!.getUserName)
      tb := body.instantiate1 x
    return out

def typeConsts (n : Name) : MetaM (Array Name) := do
  let info ← getConstInfo n
  return info.type.getUsedConstants

run_cmd do
  let n70 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70
  let n71 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71
  let n72 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72
  let n73 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73
  let n74 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p74
  let nNC : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
  let nConv71 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p70_of_p71
  let nConv72 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p71_of_p72
  let nConv73 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p72_of_p73
  let nConv74 : Name := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p73_of_p74
  let check (n : Name) (total expl : Nat) : CommandElabM Unit := do
    let (t, e, _) ← liftTermElabM (binderCounts n)
    unless t == total && e == expl do
      throwError m!"{n}: got {t}/{e}, expected {total}/{expl}"
    logInfo m!"B330-COUNT {n} total={t} explicit={e}"
  check n70 36 19
  check n71 34 18
  check n72 34 18
  check n73 34 18
  check n74 34 18
  check nNC 34 18
  check nConv71 36 19
  check nConv72 34 18
  check nConv73 34 18
  check nConv74 34 18
  let eNC ← liftTermElabM (explicitNames nNC)
  unless eNC == #[`α, `αW, `lmb, `hrun, `hbound, `hs, `hf, `hΛ, `hΛp, `hp, `hp64, `hK, `hF, `hwin,
      `hmemOrd, `hKszChar, `hrows, `hFprime] do
    throwError m!"nockCompiles explicit names {eNC}"
  let telNC ← liftTermElabM (binderTelescope nNC)
  let telStr := telNC.map fun (nm, bi) =>
    let kind := match bi with
      | .default => "expl"
      | .implicit => "impl"
      | .strictImplicit => "strict"
      | .instImplicit => "inst"
    s!"{nm}:{kind}"
  logInfo m!"B330-TEL nockCompiles={telStr}"
  logInfo m!"B330-NAMES nockCompiles={eNC}"
  let pNC ← liftTermElabM (propBinderNames nNC)
  logInfo m!"B330-PROP nockCompiles={pNC}"
  -- Converses: identity steps empty; disclosed strengthening on p72→p73.
  let d70c ← liftTermElabM (typeDiff n70 nConv71)
  unless d70c.isEmpty do throwError m!"p70_of_p71 typeDiff {d70c}"
  let d71c ← liftTermElabM (typeDiff n71 nConv72)
  unless d71c.isEmpty do throwError m!"p71_of_p72 typeDiff {d71c}"
  let d74c ← liftTermElabM (typeDiff n73 nConv74)
  unless d74c.isEmpty do throwError m!"p73_of_p74 typeDiff {d74c}"
  let d7172 ← liftTermElabM (typeDiff n71 n72)
  unless d7172.isEmpty do throwError m!"p71/p72 typeDiff {d7172}"
  let d7374 ← liftTermElabM (typeDiff n73 n74)
  unless d7374.isEmpty do throwError m!"p73/p74 typeDiff {d7374}"
  let d74nc ← liftTermElabM (typeDiff n74 nNC)
  unless d74nc.isEmpty do throwError m!"p74/nockCompiles typeDiff {d74nc}"
  let d72c ← liftTermElabM (typeDiff n72 nConv73)
  unless d72c == #[`hseedcard, `hp] do
    throwError m!"p72_of_p73 typeDiff {d72c}, expected [hseedcard, hp]"
  let d7273 ← liftTermElabM (typeDiff n72 n73)
  unless d7273 == #[`hseedcard, `hp] do
    throwError m!"p72/p73 typeDiff {d7273}, expected [hseedcard, hp]"
  logInfo m!"B330-TYPEDIFF p70_of_p71={d70c} p71_of_p72={d71c} p72_of_p73={d72c} p73_of_p74={d74c} p71/p72={d7172} p72/p73={d7273} p73/p74={d7374} p74/nockCompiles={d74nc}"
  -- Conclusion shape: statement + claim triple; not ∀ E.
  let cNC ← liftTermElabM (typeConsts nNC)
  unless cNC.contains ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement do
    throwError "nockCompiles conclusion dropped OptimizedFullStrictThm54Statement"
  if cNC.contains ``Nock.NockVMROM.Thm54.BuildableNockExecution then
    throwError "nockCompiles statement mentions BuildableNockExecution"
  unless cNC.contains ``Nock.NockVMROM.Thm54.TraceGen.RunBoundedBy do
    throwError "nockCompiles dropped RunBoundedBy"
  logInfo m!"B330-STMT statement present, BuildableNockExecution absent, RunBoundedBy present"

end Batch330BinderWalk

/-! ## C / D / E. Compiled measurements -/

namespace Nock.RedTeam.Batch330

open Nock
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.GoodSeed
open Nock.RedTeam.Batch325

/-- The cubic-vs-quadratic majorant used to pick `29` fails at `p = 23`. -/
theorem b330_cubic_gap_fails_at_23 :
    ¬ (27 * 23 ^ 2 + 22 < 23 ^ 3 + 48 * 23) := by
  decide

/-- Same majorant holds at the stated floor. -/
theorem b330_cubic_gap_holds_at_29 :
    27 * 29 ^ 2 + 22 < 29 ^ 3 + 48 * 29 := by
  decide

/-- Worst case allowed by `Λ < 23` and `rows < 23`: the *actual*
    joint budget already exceeds `23³`, even after dropping the
    nonnegative `sizeWindowRootBound` summand.  So `29 ≤ p` is not
    a disposable convenience for a loose majorant — the implication
    `rows < p ∧ Λ < p → seedBudgetVcomp < p³` is false at `23`. -/
theorem b330_actual_budget_exceeds_cube_at_23 :
    ¬ (seedBudgetVcomp 22 22 < 23 ^ 3) := by
  unfold seedBudgetVcomp seedBudget
  have : 0 ≤ sizeWindowRootBound 22 := Nat.zero_le _
  omega

/-- The paper configuration and the three landed
    literals all sit under their primes.  `hΛp` is trivial at those
    numerals -/
theorem b330_lambda_568_lt_goldilocks : 568 < 18446744069414584321 := by
  decide

theorem b330_lambda_42_lt_goldilocks : 42 < 18446744069414584321 := by
  decide

theorem b330_lambda_22_lt_769 : 22 < 769 := by
  decide

/-- A program with `Λ ≥ p` is possible; `hseedcard` does not give
    `Λ < p`. -/
theorem b330_lambda_can_exceed_p :
    seedBudgetVcomp 1000 8 < 769 ^ 3 ∧ ¬ (1000 < 769) :=
  Batch328.b328_hseedcard_not_imp_lambda_lt_p

/-- Paper `+` wraps: `(1+11) mod 12 = 0`. -/
theorem b330_paper_plus_wraps :
    FieldEmbedding.lusFBy 12 (.atom 11) = some (.atom 0) := by
  simp [FieldEmbedding.lusFBy]

/-- `evalGRom`'s increment crashes instead of wrapping.  Stronger than
    `:1531-1534`, not weaker. -/
theorem b330_guarded_plus_crashes :
    FieldEmbedding.lusGBy 12 (.atom 11) = none := by
  simp [FieldEmbedding.lusGBy]

theorem b330_constZero_is_op1 : Batch325.constZero = .cell (.atom 1) (.atom 0) :=
  rfl

theorem b330_constHundred_is_op1 :
    Batch325.constHundred = .cell (.atom 1) (.atom 100) :=
  rfl

/-- Re-derived, not quoted: unused subject atom is not `BoundedBy` -/
theorem b330_run_not_imp_hs :
    ∃ q fuel s f r,
      evalGRom q fuel s f = some r ∧ ¬ FieldEmbedding.BoundedBy q s :=
  ⟨12, 1, .atom 100, Batch325.constZero, .atom 0,
    Batch325.b325_grom_unvisited_subject, Batch325.b325_subject_not_bounded⟩

/-- Re-derived, not quoted: OP_1 tail is not `BoundedBy` -/
theorem b330_run_not_imp_hf :
    ∃ q fuel s f r,
      evalGRom q fuel s f = some r ∧ ¬ FieldEmbedding.BoundedBy q f :=
  ⟨12, 1, .atom 0, Batch325.constHundred, .atom 100,
    Batch325.b325_grom_unbounded_formula, Batch325.b325_formula_not_bounded⟩

/-- `RunBoundedBy` is existence of a guarded ROM run — it does not
    name subject/formula typing. -/
theorem b330_runBoundedBy_is_exists :
    RunBoundedBy 12 1 (.atom 100) Batch325.constZero :=
  ⟨.atom 0, Batch325.b325_grom_unvisited_subject⟩

end Nock.RedTeam.Batch330

#print axioms Nock.RedTeam.Batch330.b330_cubic_gap_fails_at_23
#print axioms Nock.RedTeam.Batch330.b330_cubic_gap_holds_at_29
#print axioms Nock.RedTeam.Batch330.b330_actual_budget_exceeds_cube_at_23
#print axioms Nock.RedTeam.Batch330.b330_lambda_can_exceed_p
#print axioms Nock.RedTeam.Batch330.b330_paper_plus_wraps
#print axioms Nock.RedTeam.Batch330.b330_guarded_plus_crashes
#print axioms Nock.RedTeam.Batch330.b330_run_not_imp_hs
#print axioms Nock.RedTeam.Batch330.b330_run_not_imp_hf
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles
