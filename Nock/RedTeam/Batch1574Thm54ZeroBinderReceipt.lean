import Lean
import Nock.RedTeam.Batch1570Thm54ZeroBinderDot
import Nock.RedTeam.Batch1572Thm54ZeroBinderRows97
import Nock.RedTeam.Batch1573Thm54ZeroBinderRows193

/-! Checks that each hostile-event theorem for the dot operator and Nock operators 0 through 9 has zero explicit binders, and prints the axioms of each. -/

open Lean Elab Command Meta

namespace Batch1574BinderWalk

def explicitBinders (n : Name) : MetaM Nat := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut e := 0
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo == .default then e := e + 1
    return e

run_cmd do
  for n in [
      ``Nock.RedTeam.Batch1570.b1570_dot_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op1_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op0_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op4_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op3_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op5_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op7_hostile,
      ``Nock.RedTeam.Batch1572.b1572_op8_hostile,
      ``Nock.RedTeam.Batch1573.b1573_op2_hostile,
      ``Nock.RedTeam.Batch1573.b1573_op6_hostile,
      ``Nock.RedTeam.Batch1573.b1573_op9_hostile] do
    let e ← liftTermElabM (explicitBinders n)
    unless e == 0 do throwError m!"{n}: {e} explicit binders, expected 0"
    logInfo m!"BINDER-WALK {n}: 0 explicit binders"

end Batch1574BinderWalk

#print axioms Nock.RedTeam.Batch1570.b1570_dot_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op1_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op0_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op4_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op3_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op5_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op7_hostile
#print axioms Nock.RedTeam.Batch1572.b1572_op8_hostile
#print axioms Nock.RedTeam.Batch1573.b1573_op2_hostile
#print axioms Nock.RedTeam.Batch1573.b1573_op6_hostile
#print axioms Nock.RedTeam.Batch1573.b1573_op9_hostile
